import numpy as np
from sklearn.decomposition import PCA

def observable_fingerprint_distance_like(X1, X2, obs_mask=None):
    """
    Lean observable_fingerprint_distance realized in PCA space.
    """

    X1 = np.asarray(X1)
    X2 = np.asarray(X2)

    # -------------------------
    # 1. Shared observer model (Lean: obs)
    # -------------------------
    X = np.vstack([X1, X2])

    pca = PCA(n_components=1).fit(X)
    mean = pca.mean_
    axis = pca.components_[0]

    def residual(X):
        proj = ((X - mean) @ axis[:, None]) * axis + mean
        return X - proj

    R1 = residual(X1)
    R2 = residual(X2)

    # -------------------------
    # 2. Structural difference (Lean: symmetric difference analogue)
    # -------------------------
    # magnitude mismatch of unexplained structure
    structure_diff = np.mean(np.linalg.norm(R1 - R2, axis=1)**2)

    # -------------------------
    # 3. Directional mismatch (Lean: tilt_map difference)
    # -------------------------
    def normalize(v):
        n = np.linalg.norm(v, axis=1, keepdims=True) + 1e-12
        return v / n

    S1 = normalize(R1)
    S2 = normalize(R2)

    tilt_diff = np.mean(np.linalg.norm(S1 - S2, axis=1)**2)

    # -------------------------
    # 4. Drift analogue (global shift difference)
    # -------------------------
    drift_diff = np.linalg.norm(np.mean(X1, axis=0) - np.mean(X2, axis=0))**2

    # -------------------------
    # 5. Full observable fingerprint distance
    # -------------------------
    D = structure_diff + tilt_diff + drift_diff

    return D
