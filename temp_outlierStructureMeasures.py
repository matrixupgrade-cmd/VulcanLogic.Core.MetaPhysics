rng = np.random.default_rng(42)
main = rng.normal(loc=[0, 0], scale=1.0, size=(500, 2))

# Unipolar: all outliers escape in one direction
uni   = rng.normal(loc=[6, 2],   scale=0.4, size=(18, 2))
# Bipolar: outliers escape in two opposite directions
bi    = np.vstack([rng.normal([ 6,  2], 0.4, (9, 2)),
                   rng.normal([-6, -2], 0.4, (9, 2))])
# Noise: random scatter
noise = rng.uniform(-8, 8, size=(18, 2))

for label, X in [("unipolar", np.vstack([main, uni])),
                 ("bipolar",  np.vstack([main, bi])),
                 ("noise",    np.vstack([main, noise]))]:
    r = basin_escape_confidence(X)
    print(f"{label:10s}  C={r['C']:.3f}  mode={r['mode']:10s}"
          f"  V_eff={r['V_eff']:.3f}  adj_L={r['adjusted_L']:.3f}"
          f"  p={r['p_value_pc1']:.3f}")
