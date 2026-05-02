import numpy as np
from sklearn.decomposition import PCA
from scipy import stats


def basin_escape_confidence(X_main, X_alt, n_boot=500):
    """
    Empirical estimator of causal escape from basin shadow.

    Connects to the Lean graph theorem:
      - observer = fixed PCA fit on X_main (the basin model)
      - observable_distance = separation in residual space
        after projecting out the basin axis
      - bootstrap = null distribution under H0: alt is just
        a resample from the basin (no causal escape)
      - C = how far the true separation exceeds that null

    Parameters
    ----------
    X_main : (n, d)  inlier / basin population
    X_alt  : (m, d)  candidate escape population
    n_boot : number of bootstrap samples for null distribution

    Returns
    -------
    dict with keys matching basin_escape_confidence from earlier:
        C             – escape confidence (separation beyond noise floor)
        p_value_pc1   – fraction of null samples >= observed distance
        V_eff         – variance explained by basin axis (observer quality)
        adjusted_L    – signal-to-noise of the separation
        mode          – 'unipolar', 'bipolar', or 'noise'
    """
    X_main = np.asarray(X_main, dtype=float)
    X_alt  = np.asarray(X_alt,  dtype=float)
    n_main, d = X_main.shape
    n_alt      = len(X_alt)

    # ── 1. Fix the observer on the basin population alone ────────────────
    # Lean: obs is fixed before comparing traces.
    # PCA on X_main = the basin's dominant causal axis.
    # This is the "functor" from the full graph to the observable quotient.
    pca   = PCA(n_components=1).fit(X_main)
    axis  = pca.components_[0]   # (d,)  fixed observer direction
    mean  = pca.mean_            # (d,)  basin center
    V_eff = float(pca.explained_variance_ratio_[0])

    # ── 2. Project both populations through the SAME observer ────────────
    # Lean: project_graph B G — same B applied to both G₁ and G₂.
    # Residual = component perpendicular to basin axis.
    # High residual norm = escaped the observer's model.
    def residual(X):
        centered   = X - mean
        proj_coeff = centered @ axis          # (n,)
        proj_vec   = np.outer(proj_coeff, axis)  # (n, d)
        return centered - proj_vec            # (n, d)  ⊥ to basin axis

    def signed_projection(X):
        """Scalar projection onto basin axis — for mode classification."""
        return (X - mean) @ axis              # (n,)

    R_main = residual(X_main)   # should be near zero by construction
    R_alt  = residual(X_alt)    # nonzero if alt has escaped the basin

    # ── 3. Observable distance in residual space ─────────────────────────
    # Lean: observable_distance B G₁ G₂ counts differing edges outside B.
    # Here: mean squared residual norm of alt, minus that of main.
    # Measures how much structure alt has that the observer cannot explain.
    def escape_score(R_a, R_b):
        """
        Symmetrized residual separation.
        Zero if alt looks like main in residual space.
        Positive if alt has structure main does not.
        """
        mean_R_a = np.mean(np.sum(R_a**2, axis=1))  # mean ||residual||²
        mean_R_b = np.mean(np.sum(R_b**2, axis=1))
        # Also capture directional difference (tilt term from earlier)
        dir_a = R_a / (np.linalg.norm(R_a, axis=1, keepdims=True) + 1e-12)
        dir_b = R_b / (np.linalg.norm(R_b, axis=1, keepdims=True) + 1e-12)
        tilt  = np.sum((dir_a.mean(0) - dir_b.mean(0))**2)
        return abs(mean_R_a - mean_R_b) + tilt

    base_dist = escape_score(R_main, R_alt)

    # ── 4. Null distribution: what if alt were just basin resamples? ──────
    # Bootstrap draws from X_main only — this is the null hypothesis
    # that no causal escape has occurred (alt is just noise from the basin).
    # Lean analogue: basin_masks holds for all n — no escape exists.
    null_scores = []
    for _ in range(n_boot):
        idx_a = np.random.choice(n_main, n_main, replace=True)
        idx_b = np.random.choice(n_main, n_alt,  replace=True)  # same size as alt
        R_a   = residual(X_main[idx_a])
        R_b   = residual(X_main[idx_b])
        null_scores.append(escape_score(R_a, R_b))

    null_scores = np.array(null_scores)
    null_mean   = float(null_scores.mean())
    null_std    = float(null_scores.std() + 1e-8)

    # ── 5. Escape confidence and p-value ─────────────────────────────────
    # p_value: how often does pure basin resampling produce >= base_dist?
    # Low p → the observed separation is unlikely under the null.
    p_value = float(np.mean(null_scores >= base_dist))

    # C: separation beyond the null floor, in units of null std
    # Clipped to [0, 1] via sigmoid-like normalisation
    z_score = (base_dist - null_mean) / null_std
    C       = float(1 / (1 + np.exp(-z_score + 2)))  # shifted sigmoid

    # adjusted_L: raw signal-to-noise ratio
    adjusted_L = float(base_dist / null_std)

    # ── 6. Mode classification ────────────────────────────────────────────
    # Lean: basin_escape witness (i, j) tells you WHICH edges differ.
    # Here: sign distribution of alt projections onto basin axis.
    # Unipolar  → alt escapes in one direction (sign_ratio near 0 or 1)
    # Bipolar   → alt escapes in both directions (sign_ratio near 0.5,
    #             but with high spread)
    # Noise     → low residual norm, no coherent escape
    proj_alt   = signed_projection(X_alt)
    sign_ratio = float((proj_alt > 0).mean())
    resid_norm = float(np.mean(np.sum(R_alt**2, axis=1)))
    null_resid = float(np.mean(np.sum(R_main**2, axis=1)))

    if resid_norm < 1.5 * null_resid or V_eff > 0.85:
        mode = 'noise'
    elif sign_ratio > 0.75 or sign_ratio < 0.25:
        mode = 'unipolar'
    elif 0.35 < sign_ratio < 0.65:
        mode = 'bipolar'
    else:
        mode = 'noise'

    return {
        "C"           : round(C, 4),
        "p_value_pc1" : round(p_value, 4),
        "V_eff"       : round(V_eff, 4),
        "adjusted_L"  : round(adjusted_L, 4),
        "mode"        : mode,
    }
