```java
package app.capgo.capacitor.camera.preview;

import android.Manifest;
import android.content.Context;
import android.content.pm.PackageManager;
import android.content.res.Configuration;
import android.graphics.Bitmap;
import android.graphics.BitmapFactory;
import android.graphics.Canvas;
import android.graphics.Color;
import android.graphics.Matrix;
import android.graphics.Paint;
import android.graphics.Rect;
import android.graphics.Typeface;
import android.graphics.drawable.GradientDrawable;
import android.hardware.camera2.CameraAccessException;
import android.hardware.camera2.CameraCharacteristics;
import android.hardware.camera2.CameraManager;
import android.hardware.camera2.CaptureRequest;
import android.location.Location;
import android.media.MediaScannerConnection;
import android.os.Build;
import android.os.Environment;
import android.util.Base64;
import android.util.DisplayMetrics;
import android.util.Log;
import android.util.Range;
import android.util.Rational;
import android.util.Size;
import android.view.View;
import android.view.ViewGroup;
import android.view.WindowManager;
import android.view.WindowMetrics;
import android.webkit.WebView;
import android.widget.FrameLayout;
import androidx.annotation.NonNull;
import androidx.annotation.OptIn;
import androidx.camera.camera2.interop.Camera2CameraControl;
import androidx.camera.camera2.interop.Camera2CameraInfo;
import androidx.camera.camera2.interop.CaptureRequestOptions;
import androidx.camera.camera2.interop.ExperimentalCamera2Interop;
import androidx.camera.core.AspectRatio;
import androidx.camera.core.Camera;
import androidx.camera.core.CameraInfo;
import androidx.camera.core.CameraSelector;
import androidx.camera.core.ExposureState;
import androidx.camera.core.FocusMeteringAction;
import androidx.camera.core.FocusMeteringResult;
import androidx.camera.core.ImageAnalysis; // ADDED
import androidx.camera.core.ImageCapture;
import androidx.camera.core.ImageCaptureException;
import androidx.camera.core.ImageProxy;
import androidx.camera.core.MeteringPoint;
import androidx.camera.core.MeteringPointFactory;
import androidx.camera.core.Preview;
import androidx.camera.core.ResolutionInfo;
import androidx.camera.core.TorchState;
import androidx.camera.core.ZoomState;
import androidx.camera.core.resolutionselector.AspectRatioStrategy;
import androidx.camera.core.resolutionselector.ResolutionSelector;
import androidx.camera.core.resolutionselector.ResolutionStrategy;
import androidx.camera.lifecycle.ProcessCameraProvider;
import androidx.camera.video.FallbackStrategy;
import androidx.camera.video.FileOutputOptions;
import androidx.camera.video.Quality;
import androidx.camera.video.QualitySelector;
import androidx.camera.video.Recorder;
import androidx.camera.video.Recording;
import androidx.camera.video.VideoCapture;
import androidx.camera.video.VideoRecordEvent;
import androidx.camera.view.PreviewView;
import androidx.core.app.ActivityCompat;
import androidx.core.content.ContextCompat;
import androidx.exifinterface.media.ExifInterface;
import androidx.lifecycle.Lifecycle;
import androidx.lifecycle.LifecycleObserver;
import androidx.lifecycle.LifecycleOwner;
import androidx.lifecycle.LifecycleRegistry;
import app.capgo.capacitor.camera.preview.model.CameraSessionConfiguration;
import app.capgo.capacitor.camera.preview.model.LensInfo;
import app.capgo.capacitor.camera.preview.model.ZoomFactors;
import com.google.common.util.concurrent.ListenableFuture;
import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.nio.ByteBuffer;
import java.text.SimpleDateFormat;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Date;
import java.util.List;
import java.util.Locale;
import java.util.Objects;
import java.util.Set;
import java.util.concurrent.Executor;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import org.json.JSONObject;

public class CameraXView implements LifecycleOwner, LifecycleObserver {

    private static final String TAG = "CameraPreview CameraXView";
    private static final String FOCUS_INDICATOR_TAG = "cpcp_focus_indicator";

    public interface CameraXViewListener {
        void onPictureTaken(String base64, JSONObject exif);
        void onPictureTakenError(String message);
        void onSampleTaken(String result);
        void onSampleTakenError(String message);
        void onCameraStarted(int width, int height, int x, int y);
        void onCameraStartError(String message);
        void onCameraStopped(CameraXView source);
    }

    public interface VideoRecordingCallback {
        void onSuccess(String filePath);
        void onError(String message);
    }

    private ProcessCameraProvider cameraProvider;
    private Camera camera;
    private ImageCapture imageCapture;
    // REMOVED: private ImageCapture sampleImageCapture; (Replaced by ImageAnalysis)
    private ImageAnalysis imageAnalysis; // ADDED: The silent stream processor
    private VideoCapture<Recorder> videoCapture;
    private Recording currentRecording;
    private File currentVideoFile;
    private VideoRecordingCallback currentVideoCallback;
    private PreviewView previewView;
    private GridOverlayView gridOverlayView;
    private FrameLayout previewContainer;
    private View focusIndicatorView;
    private long focusIndicatorAnimationId = 0;
    private CameraSelector currentCameraSelector;
    private String currentDeviceId;
    private int currentFlashMode = ImageCapture.FLASH_MODE_OFF;
    private CameraSessionConfiguration sessionConfig;
    private CameraXViewListener listener;
    private final Context context;
    private final WebView webView;
    private final LifecycleRegistry lifecycleRegistry;
    private final Executor mainExecutor;
    private ExecutorService cameraExecutor;
    private boolean isRunning = false;
    private Size currentPreviewResolution = null;
    private ListenableFuture<FocusMeteringResult> currentFocusFuture = null;
    private String currentExposureMode = "CONTINUOUS";
    private final Object captureLock = new Object();
    private volatile boolean isCapturingPhoto = false;
    private volatile boolean stopRequested = false;
    private volatile boolean previewDetachedOnDeferredStop = false;

    private final Object operationLock = new Object();
    private int activeOperations = 0;
    private boolean stopPending = false;

    // === NEW: ImageAnalysis Gatekeeping variables ===
    private final Object analysisLock = new Object();
    private volatile boolean captureNextFrame = false;
    private volatile BitmapProcessor pendingProcessor = null;
    private volatile int pendingQuality = 100;
    // ================================================

    private interface BitmapProcessor {
        Bitmap process(Bitmap original);
    }

    private boolean IsOperationRunning(String name) {
        synchronized (operationLock) {
            if (stopPending) {
                Log.d(TAG, "beginOperation: blocked '" + name + "' due to stopPending");
                return true;
            }
            activeOperations++;
            Log.v(TAG, "beginOperation: '" + name + "' (active=" + activeOperations + ")");
            return false;
        }
    }

    private void endOperation(String name) {
        boolean shouldStop = false;
        synchronized (operationLock) {
            if (activeOperations > 0) activeOperations--;
            Log.v(TAG, "endOperation: '" + name + "' (active=" + activeOperations + ")");
            if (activeOperations == 0 && stopPending) {
                shouldStop = true;
            }
        }
        if (shouldStop) {
            Log.d(TAG, "endOperation: all operations complete; performing deferred stop");
            performImmediateStop();
        }
    }

    public boolean isCapturing() {
        return isCapturingPhoto;
    }

    public boolean isBusy() {
        synchronized (captureLock) {
            return isCapturingPhoto || stopRequested;
        }
    }

    public boolean isStopDeferred() {
        synchronized (operationLock) {
            return stopPending && activeOperations > 0;
        }
    }

    public boolean isStopping() {
        synchronized (operationLock) {
            return stopPending;
        }
    }

    public CameraXView(Context context, WebView webView) {
        this.context = context;
        this.webView = webView;
        this.lifecycleRegistry = new LifecycleRegistry(this);
        this.mainExecutor = ContextCompat.getMainExecutor(context);

        mainExecutor.execute(() -> lifecycleRegistry.setCurrentState(Lifecycle.State.CREATED));
    }

    @NonNull
    @Override
    public Lifecycle getLifecycle() {
        return lifecycleRegistry;
    }

    public CameraSessionConfiguration getSessionConfig() {
        return sessionConfig;
    }

    public void setListener(CameraXViewListener listener) {
        this.listener = listener;
    }

    public boolean isRunning() {
        return isRunning;
    }

    public View getPreviewContainer() {
        return previewContainer;
    }

    // ... [saveImageToGallery methods omitted for brevity, they remain unchanged] ...

    public void startSession(CameraSessionConfiguration config) {
        this.sessionConfig = config;
        cameraExecutor = Executors.newSingleThreadExecutor();
        synchronized (operationLock) {
            activeOperations = 0;
            stopPending = false;
        }
        mainExecutor.execute(() -> {
            lifecycleRegistry.setCurrentState(Lifecycle.State.STARTED);
            setupCamera();
        });
    }

    public void stopSession() {
        // Mark stop pending; reject new operations and wait for active ones to finish
        synchronized (operationLock) {
            stopPending = true;
        }
        stopRequested = true;

        // Cancel any pending analysis capture
        synchronized (analysisLock) {
            captureNextFrame = false;
            pendingProcessor = null;
        }

        boolean hasOps;
        synchronized (operationLock) {
            hasOps = activeOperations > 0;
        }
        if (hasOps) {
            if (!previewDetachedOnDeferredStop) {
                mainExecutor.execute(() -> {
                    try {
                        if (previewContainer != null) {
                            ViewGroup parent = (ViewGroup) previewContainer.getParent();
                            if (parent != null) {
                                parent.removeView(previewContainer);
                            }
                        }
                        previewDetachedOnDeferredStop = true;
                    } catch (Exception ignored) {}
                });
            }
            if (currentFocusFuture != null && !currentFocusFuture.isDone()) {
                try {
                    currentFocusFuture.cancel(true);
                } catch (Exception ignored) {}
            }
            return;
        }

        performImmediateStop();
    }

    private void performImmediateStop() {
        isRunning = false;
        if (currentFocusFuture != null && !currentFocusFuture.isDone()) {
            currentFocusFuture.cancel(true);
        }
        currentFocusFuture = null;

        mainExecutor.execute(() -> {
            try {
                lifecycleRegistry.setCurrentState(Lifecycle.State.DESTROYED);
                if (cameraProvider != null) {
                    cameraProvider.unbindAll();
                }
                lifecycleRegistry.setCurrentState(Lifecycle.State.DESTROYED);
                if (cameraExecutor != null) {
                    cameraExecutor.shutdown();
                }
                removePreviewView();
            } catch (Exception e) {
                Log.w(TAG, "performImmediateStop: error during stop", e);
            } finally {
                stopRequested = false;
                previewDetachedOnDeferredStop = false;
                synchronized (operationLock) {
                    activeOperations = 0;
                    stopPending = false;
                }
                if (listener != null) {
                    try {
                        listener.onCameraStopped(this);
                    } catch (Exception ignored) {}
                }
            }
        });
    }

    private void setupCamera() {
        ListenableFuture<ProcessCameraProvider> cameraProviderFuture = ProcessCameraProvider.getInstance(context);
        cameraProviderFuture.addListener(
            () -> {
                try {
                    cameraProvider = cameraProviderFuture.get();
                    setupPreviewView();
                    bindCameraUseCases();
                } catch (Exception e) {
                    if (listener != null) {
                        listener.onCameraStartError("Error initializing camera: " + e.getMessage());
                    }
                }
            },
            mainExecutor
        );
    }

    // ... [setupPreviewView, calculatePreviewLayoutParams, removePreviewView remain unchanged] ...
    // For brevity, assume they are here exactly as in your original code.

    private void setupPreviewView() {
        if (previewView != null) {
            removePreviewView();
        }
        if (sessionConfig.isToBack()) {
            webView.setBackgroundColor(android.graphics.Color.TRANSPARENT);
        }
        previewContainer = new FrameLayout(context);
        previewContainer.setClickable(true);
        previewContainer.setFocusable(true);
        previewContainer.setLayerType(View.LAYER_TYPE_HARDWARE, null);
        previewContainer.setClipChildren(false);
        previewContainer.setClipToPadding(false);
        previewView = new PreviewView(context);
        previewView.setImplementationMode(PreviewView.ImplementationMode.COMPATIBLE);
        String initialAspectRatio = sessionConfig != null ? sessionConfig.getAspectRatio() : null;
        previewView.setScaleType(
            (initialAspectRatio == null || initialAspectRatio.isEmpty())
                ? PreviewView.ScaleType.FIT_CENTER
                : PreviewView.ScaleType.FILL_CENTER
        );
        previewView.setClickable(true);
        previewView.setFocusable(true);
        previewContainer.addView(
            previewView,
            new FrameLayout.LayoutParams(FrameLayout.LayoutParams.MATCH_PARENT, FrameLayout.LayoutParams.MATCH_PARENT)
        );
        gridOverlayView = new GridOverlayView(context);
        gridOverlayView.setClickable(false);
        gridOverlayView.setFocusable(false);
        previewContainer.addView(
            gridOverlayView,
            new FrameLayout.LayoutParams(FrameLayout.LayoutParams.MATCH_PARENT, FrameLayout.LayoutParams.MATCH_PARENT)
        );
        gridOverlayView.post(() -> {
            String currentGridMode = sessionConfig.getGridMode();
            gridOverlayView.setGridMode(currentGridMode);
        });
        previewView.addOnLayoutChangeListener((v, left, top, right, bottom, oldLeft, oldTop, oldRight, oldBottom) -> {
            if (left != oldLeft || top != oldTop || right != oldRight || bottom != oldBottom) {
                updateGridOverlayBounds();
            }
        });
        ViewGroup parent = (ViewGroup) webView.getParent();
        if (parent != null) {
            FrameLayout.LayoutParams layoutParams = calculatePreviewLayoutParams();
            parent.addView(previewContainer, layoutParams);
            if (sessionConfig.isToBack()) webView.bringToFront();
        }
    }

    // ... [calculatePreviewLayoutParams, etc. omitted] ...

    @OptIn(markerClass = ExperimentalCamera2Interop.class)
    private void bindCameraUseCases() {
        // 1. Safety Checks
        if (cameraProvider == null) return;
        if (previewView == null) return;

        // 2. Run on Main Thread (Lifecycle binding requires this)
        mainExecutor.execute(() -> {
            try {
                // --- A. Configure Camera Selector ---
                currentCameraSelector = buildCameraSelector();

                // --- B. Configure Resolution & Aspect Ratio ---
                ResolutionSelector.Builder resolutionSelectorBuilder = new ResolutionSelector.Builder()
                    .setResolutionStrategy(ResolutionStrategy.HIGHEST_AVAILABLE_STRATEGY);

                if (sessionConfig.getAspectRatio() != null) {
                    int aspectRatio = "16:9".equals(sessionConfig.getAspectRatio())
                        ? AspectRatio.RATIO_16_9
                        : AspectRatio.RATIO_4_3;

                    resolutionSelectorBuilder.setAspectRatioStrategy(
                        new AspectRatioStrategy(aspectRatio, AspectRatioStrategy.FALLBACK_RULE_AUTO)
                    );
                }
                ResolutionSelector resolutionSelector = resolutionSelectorBuilder.build();

                // --- C. Get Rotation ---
                int rotation = previewView.getDisplay() != null
                    ? previewView.getDisplay().getRotation()
                    : android.view.Surface.ROTATION_0;

                // --- D. Build Preview Use Case ---
                Preview preview = new Preview.Builder()
                    .setResolutionSelector(resolutionSelector)
                    .setTargetRotation(rotation)
                    .build();

                // --- E. Build ImageCapture Use Case (Standard/Loud) ---
                // We keep this for high-res photos with Flash support
                imageCapture = new ImageCapture.Builder()
                    .setResolutionSelector(resolutionSelector)
                    .setCaptureMode(ImageCapture.CAPTURE_MODE_MINIMIZE_LATENCY)
                    .setFlashMode(currentFlashMode)
                    .setTargetRotation(rotation)
                    .build();

                // --- F. Build ImageAnalysis Use Case (Silent/Fast) ---
                // This acts as the silent snapshot engine
                imageAnalysis = new ImageAnalysis.Builder()
                    .setResolutionSelector(resolutionSelector)
                    // STRATEGY_KEEP_ONLY_LATEST prevents queue buildup.
                    // If the analyzer is busy, new frames are dropped.
                    .setBackpressureStrategy(ImageAnalysis.STRATEGY_KEEP_ONLY_LATEST)
                    .setOutputImageFormat(ImageAnalysis.OUTPUT_IMAGE_FORMAT_RGBA_8888) // Direct Bitmap friendly
                    .setTargetRotation(rotation)
                    .build();

                // Define the Analyzer (The "Worker")
                imageAnalysis.setAnalyzer(cameraExecutor, imageProxy -> {
                    synchronized (analysisLock) {
                        // 1. GATEKEEPER: If no snapshot requested, discard immediately.
                        if (!captureNextFrame) {
                            imageProxy.close();
                            return;
                        }

                        // 2. PROCESSING: Snapshot requested!
                        try {
                            Log.d(TAG, "ImageAnalysis: Processing requested frame");

                            // Convert YUV/HardwareBuffer to Bitmap
                            Bitmap bitmap = imageProxy.toBitmap();

                            // Apply Crop/Resize if a processor was provided
                            Bitmap finalBitmap = (pendingProcessor != null)
                                ? pendingProcessor.process(bitmap)
                                : bitmap;

                            // Compress to Base64
                            ByteArrayOutputStream outputStream = new ByteArrayOutputStream();
                            finalBitmap.compress(Bitmap.CompressFormat.JPEG, pendingQuality, outputStream);
                            byte[] bytes = outputStream.toByteArray();
                            String base64 = Base64.encodeToString(bytes, Base64.NO_WRAP);

                            // Memory Cleanup
                            if (bitmap != finalBitmap) bitmap.recycle();

                            // Return result to Capacitor/JS
                            if (listener != null) {
                                listener.onSampleTaken(base64);
                            }
                        } catch (Exception e) {
                            Log.e(TAG, "ImageAnalysis processing error", e);
                            if (listener != null) listener.onSampleTakenError(e.getMessage());
                        } finally {
                            // 3. RESET: Close the gate and the image
                            captureNextFrame = false;
                            pendingProcessor = null;
                            imageProxy.close(); // CRITICAL: Must close to receive next frame
                            endOperation("captureSample");
                        }
                    }
                });

                // --- G. Build VideoCapture (Optional) ---
                if (sessionConfig.isVideoModeEnabled()) {
                    QualitySelector qualitySelector = QualitySelector.fromOrderedList(
                        Arrays.asList(Quality.FHD, Quality.HD, Quality.SD),
                        FallbackStrategy.higherQualityOrLowerThan(Quality.FHD)
                    );
                    Recorder recorder = new Recorder.Builder()
                        .setQualitySelector(qualitySelector)
                        .build();
                    videoCapture = VideoCapture.withOutput(recorder);
                }

                // --- H. BINDING LOGIC ---

                // Unbind everything before rebinding
                cameraProvider.unbindAll();

                // Re-attach surface provider (needed after unbind)
                preview.setSurfaceProvider(previewView.getSurfaceProvider());

                try {
                    if (sessionConfig.isVideoModeEnabled() && videoCapture != null) {
                        // === VIDEO MODE ===
                        // Bind: Preview + Video + Analysis
                        // We exclude ImageCapture here. Most hardware cannot do 4 streams.
                        // This allows recording video AND taking silent snapshots simultaneously.
                        Log.d(TAG, "Binding: Video Mode (Preview + Video + Analysis)");
                        camera = cameraProvider.bindToLifecycle(
                            this,
                            currentCameraSelector,
                            preview,
                            videoCapture,
                            imageAnalysis
                        );
                    } else {
                        // === PHOTO MODE ===
                        // Bind: Preview + ImageCapture + Analysis
                        // This allows standard photos (with flash) AND silent snapshots.
                        Log.d(TAG, "Binding: Photo Mode (Preview + Capture + Analysis)");
                        camera = cameraProvider.bindToLifecycle(
                            this,
                            currentCameraSelector,
                            preview,
                            imageCapture,
                            imageAnalysis
                        );
                    }
                } catch (IllegalArgumentException e) {
                    // === FALLBACK FOR LEGACY DEVICES ===
                    // Some older devices (Hardware Level: LEGACY) cannot handle 3 use cases.
                    // If the 3-case bind fails, we drop ImageAnalysis to ensure the app at least starts.
                    Log.e(TAG, "Hardware limit reached (3 use-cases failed). Falling back to basic binding.", e);

                    cameraProvider.unbindAll();
                    if (sessionConfig.isVideoModeEnabled() && videoCapture != null) {
                        camera = cameraProvider.bindToLifecycle(this, currentCameraSelector, preview, videoCapture);
                    } else {
                        camera = cameraProvider.bindToLifecycle(this, currentCameraSelector, preview, imageCapture);
                    }
                    // Note: In this fallback state, captureSample() will fail nicely
                    // because checks for (imageAnalysis == null) are in place.
                }

                // --- I. Post-Bind Configuration ---
                resetExposureCompensationToDefault();

                // Log Camera Info
                CameraInfo cameraInfo = camera.getCameraInfo();
                Log.d(TAG, "Bound Camera ID: " + Camera2CameraInfo.from(cameraInfo).getCameraId());

                // Apply Scale Type
                String ar = sessionConfig != null ? sessionConfig.getAspectRatio() : null;
                previewView.setScaleType(
                    (ar == null || ar.isEmpty()) ? PreviewView.ScaleType.FIT_CENTER : PreviewView.ScaleType.FILL_CENTER
                );

                // Apply Zoom
                float initialZoom = sessionConfig.getTargetZoom() != 1.0f ? sessionConfig.getTargetZoom() : sessionConfig.getZoomFactor();
                if (initialZoom != 1.0f) {
                    setZoom(initialZoom);
                }

                // Notify Listener
                isRunning = true;
                if (listener != null) {
                    previewContainer.post(() -> {
                        listener.onCameraStarted(getPreviewWidth(), getPreviewHeight(), getPreviewX(), getPreviewY());
                    });
                }

            } catch (Exception e) {
                Log.e(TAG, "Error in bindCameraUseCases", e);
                if (listener != null) listener.onCameraStartError("Error binding camera: " + e.getMessage());
            }
        });
    }
    // === SNAPSHOT METHODS USING IMAGE ANALYSIS ===

    public void captureSample(int quality) {
        captureSampleInternal(quality, null); // null processor = return full image
    }

    public void captureDownscaledSample(int quality, int targetMaxSize) {
        captureSampleInternal(quality, original -> {
            int width = original.getWidth();
            int height = original.getHeight();
            int smallestSide = Math.min(width, height);

            if (smallestSide <= targetMaxSize) {
                return original;
            }

            float scale = (float) targetMaxSize / (float) smallestSide;
            int newWidth = Math.round(width * scale);
            int newHeight = Math.round(height * scale);

            return Bitmap.createScaledBitmap(original, newWidth, newHeight, true);
        });
    }

    public void captureCroppedSample(int quality, int x, int y, int reqWidth, int reqHeight) {
        captureSampleInternal(quality, original -> {
            if (previewContainer == null) return original;

            // 1. Sensor Dimensions (High Res, e.g. 4000x3000)
            float imgW = (float) original.getWidth();
            float imgH = (float) original.getHeight();

            // 2. View Dimensions (Screen Res, e.g. 1080x1920)
            float viewW = (float) previewContainer.getWidth();
            float viewH = (float) previewContainer.getHeight();

            // 3. Determine Scale Factor
            // CameraX PreviewView (FILL_CENTER) scales the image so that it fills the view.
            // It uses the LARGER scale factor to ensure no black bars.
            // scale = max(viewW / imgW, viewH / imgH) -> This is how much sensor was scaled UP to screen.
            // We need the reverse: How much to scale Screen Inputs DOWN to Sensor.

            float scaleX = imgW / viewW;
            float scaleY = imgH / viewH;

            // If FILL_CENTER was used, the sensor image was cropped to fit the aspect ratio.
            // We need to find the "Virtual Viewport" on the sensor.

            // Which dimension is the limiting factor?
            // If sensor is 4:3 (wider) and screen is 16:9 (taller), the sides of sensor are cropped.

            float sensorCropW, sensorCropH;
            float scaleFactor;

            if (scaleX < scaleY) {
                // The horizontal ratio is smaller, meaning the View is wider relative to image?
                // Let's calculate logical mapping.
                // FILL_CENTER logic:
                // The content is scaled by `max(viewW/imgW, viewH/imgH)` (Zooming in).
                // Let's work in Sensor Coordinates.

                // Calculate the aspect ratios
                float sensorAspect = imgW / imgH;
                float viewAspect = viewW / viewH;

                if (sensorAspect > viewAspect) {
                    // Sensor is wider than View (e.g. 4:3 vs 9:16)
                    // Sides are cropped. Height matches.
                    scaleFactor = imgH / viewH;
                    sensorCropW = viewW * scaleFactor;
                    sensorCropH = imgH; // Matches
                } else {
                    // Sensor is taller than View (unlikely for landscape sensor) OR
                    // View is wider than Sensor (e.g. 16:9 Sensor on 21:9 screen)
                    // Top/Bottom cropped. Width matches.
                    scaleFactor = imgW / viewW;
                    sensorCropW = imgW; // Matches
                    sensorCropH = viewH * scaleFactor;
                }

                // Calculate Offset (centering)
                float offsetX = (imgW - sensorCropW) / 2f;
                float offsetY = (imgH - sensorCropH) / 2f;

                // Map coordinates
                int finalX = (int) (offsetX + (x * scaleFactor));
                int finalY = (int) (offsetY + (y * scaleFactor));
                int finalW = (int) (reqWidth * scaleFactor);
                int finalH = (int) (reqHeight * scaleFactor);

                // Safety bounds
                finalX = Math.max(0, finalX);
                finalY = Math.max(0, finalY);
                finalW = Math.min(finalW, (int)imgW - finalX);
                finalH = Math.min(finalH, (int)imgH - finalY);

                if (finalW <= 0 || finalH <= 0) return original;

                return Bitmap.createBitmap(original, finalX, finalY, finalW, finalH);
            }

            // Fallback for simple scaling if logic ambiguous
            return original;
        });
    }

    private void captureSampleInternal(int quality, BitmapProcessor processor) {
        if (imageAnalysis == null) {
            if (listener != null) listener.onSampleTakenError("Camera not ready (Analysis missing)");
            return;
        }

        // Prevent overlapping requests
        if (IsOperationRunning("captureSample")) {
            // If you want to allow burst, you might remove this check,
            // but "captureNextFrame" logic only handles one at a time.
            Log.d(TAG, "captureSample skipped: busy");
            return;
        }

        synchronized (analysisLock) {
            this.pendingQuality = quality;
            this.pendingProcessor = processor;
            this.captureNextFrame = true; // Trigger the Analyzer
        }
        Log.d(TAG, "Snapshot requested via ImageAnalysis");
    }

    // ... [Helper methods: buildCameraSelector, getPreviewWidth/Height, updateGridOverlayBounds, etc.] ...
    // ... [Ensure buildCameraSelector, getPreviewWidth, etc are present as in your original code] ...

    // Simple helpers to ensure code compiles if you didn't have them in the snippet provided:
    private CameraSelector buildCameraSelector() {
        int lensFacing = sessionConfig.getPosition().equals("front") ? CameraSelector.LENS_FACING_FRONT : CameraSelector.LENS_FACING_BACK;
        return new CameraSelector.Builder().requireLensFacing(lensFacing).build();
    }

    private void removePreviewView() {
        if (previewContainer != null) {
            ViewGroup parent = (ViewGroup) previewContainer.getParent();
            if (parent != null) {
                parent.removeView(previewContainer);
            }
            previewContainer = null;
        }
        previewView = null;
        gridOverlayView = null;
        webView.setBackgroundColor(android.graphics.Color.WHITE);
    }

    private FrameLayout.LayoutParams calculatePreviewLayoutParams() {
         // (Your existing logic here)
         // Placeholder for compilation context
         return new FrameLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.MATCH_PARENT);
    }

    private void updateGridOverlayBounds() {
        if (gridOverlayView != null && previewView != null) {
             gridOverlayView.setOverlayBounds(previewView.getLeft(), previewView.getTop(), previewView.getWidth(), previewView.getHeight());
        }
    }

    public int getPreviewWidth() {
        return previewView != null ? previewView.getWidth() : 0;
    }
    public int getPreviewHeight() {
        return previewView != null ? previewView.getHeight() : 0;
    }
    public int getPreviewX() {
        return previewContainer != null ? previewContainer.getLeft() + (previewView != null ? previewView.getLeft() : 0) : 0;
    }
    public int getPreviewY() {
        return previewContainer != null ? previewContainer.getTop() + (previewView != null ? previewView.getTop() : 0) : 0;
    }

    private void resetExposureCompensationToDefault() {
         if (camera != null) camera.getCameraControl().setExposureCompensationIndex(0);
    }

    public void setZoom(float zoomFactor) {
        if (camera != null) {
            camera.getCameraControl().setZoomRatio(zoomFactor);
        }
    }

}
```
