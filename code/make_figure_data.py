"""Write the data files used by the figures of the paper (data/*.dat).

Usage: python3 code/make_figure_data.py [OUT_DIR]       (OUT_DIR defaults to data/ beside code/)
Standard library only. Reads ONLY the archived files in this directory; no certified number is recomputed.
The one floating-point evaluation (fig3) is a plot of a certified quantity in double precision, not a certificate.

  fig2-run-length.dat    K L_certified L_search L_truncated_model sign
                         (summary.json, torus_results.json; L_search = L_robust of the float search, a lower bound
                         of the torus supremum; the certified rows are the theorems under LI_theta(K))
  fig2-refs.dat          name value   horizontal lines: 312 (RH, Theorem B),
                         621 (RH, Theorem A: certified window 622 minus 1)
  fig3-run-K700.dat      j F threshold margin   F_x(j) for j = 0..391 at K = 700 (double precision from
                         cert_run_pos_K700.json phases and z2000.json zero midpoints), threshold T_K
  fig4-density.dat       label kind lo hi mid   ratio delta/(theta_1/pi): kind in proved, numeric, heuristic
                         (density_results.json, b_density_results.json)
  fig1-comb-cells.dat    u_mid R_upper   Theorem A, tier L = 622: one row per certified cell of u (1024 rows),
                         u_mid the cell midpoint, R_upper the certified upper bound of the comb ratio on the cell
                         (cert_comb_622.json, field cells); all below 1
Values are written with 9 to 12 significant digits so that a re-run on another machine agrees.
"""
import json, math, os, re, sys
here = os.path.dirname(os.path.abspath(__file__))
out = sys.argv[1] if len(sys.argv) > 1 else os.path.join(here, "..", "data")
os.makedirs(out, exist_ok=True)
J = lambda f: json.load(open(os.path.join(here, f)))
def W(name, header, rows):
    with open(os.path.join(out, name), "w") as f:
        f.write("# " + header + "\n")
        for r in rows: f.write(" ".join(r) + "\n")

# ---- fig 1
from fractions import Fraction
cc = J("cert_comb_622.json")["cells"]
rows = [["%.12g" % float((Fraction(c["u_lo"]) + Fraction(c["u_hi"])) / 2), "%.12g" % float(c["R_upper"])] for c in cc]
W("fig1-comb-cells.dat", "u_mid R_upper (Theorem A, L=622: certified upper bound of the comb ratio on each of %d cells of u; all below 1)" % len(rows), rows)

# ---- fig 2
summ = {row[0]: row for row in J("summary.json")}
tor = J("torus_results.json")
rows = []
for key in sorted(tor, key=lambda s: (tor[s]["K"], s)):
    r = tor[key]
    cert = summ[key][6]
    rows.append([str(r["K"]), str(r["L_robust"]) if cert else "nan", str(r["L_robust"]), str(r["L_truncated_model"]), str(r["sign"])])
W("fig2-run-length.dat", "K L_certified L_search L_truncated_model sign (L_certified nan if not certified; L_search is a search lower bound)", rows)
W("fig2-refs.dat", "name value (312: Theorem B, RH; 621: Theorem A, RH)",
  [["rh_run_312", "312"], ["rh_window_bound", str(J("cert_comb_622.json")["L"] - 1)]])

# ---- fig 3
z = J("z2000.json"); c = J("cert_run_pos_K700.json"); K = c["K"]
gam = [z_[0] * 2.0 ** z_[1] for z_ in z["gamma_mid_man_exp_rad_man_exp"][:K]]
w = [1.0 / (0.25 + g * g) for g in gam]
th = [2 * math.atan(1.0 / (2 * g)) for g in gam]
x = [p / q for p, q in c["x_num_den"]]
T = c["T_K_float"]; sg = c["sign_stored"]
rows = []
for j in range(c["L"]):
    F = sum(2 * w[k] * math.cos(j * th[k] + x[k]) for k in range(K))
    rows.append([str(j), "%.12g" % (sg * F), "%.12g" % T, "%.9g" % (sg * F - T)])
W("fig3-run-K700.dat", "j F threshold margin (double precision plot of a certified quantity; K=700, sign %+d)" % sg, rows)

# ---- fig 4
d = J("density_results.json"); b = J("b_density_results.json")
rows = []
for name, label in (("thm4", "TheoremD"), ("thm4p", "TheoremD_trunc100")):
    lo, hi = float(d["results"][name]["lo"]), float(d["results"][name]["hi"])
    rows.append([label, "proved", "%.12g" % lo, "%.12g" % hi, "%.12g" % ((lo + hi) / 2)])
f = b["fourier"]
rows.append(["K100_fourier", "numeric", "%.12g" % f["ratio_lo"], "%.12g" % f["ratio_hi"], "%.12g" % f["ratio"]])
for e in b["K_dependence"]:
    rows.append(["K%d" % e["K"], "numeric", "%.12g" % e["ratio"], "%.12g" % e["ratio"], "%.12g" % e["ratio"]])
m = b["mc"]; rows.append(["MC_K100", "numeric", "%.9g" % (m["ratio"] - m["se_ratio"]), "%.9g" % (m["ratio"] + m["se_ratio"]), "%.9g" % m["ratio"]])
t = b["tail_zeros_heuristic"]; r0 = f["ratio"]
rows.append(["K_inf_extrapolated", "heuristic", "%.9g" % (r0 + t["band"][0]), "%.9g" % (r0 + t["band"][1]), "%.9g" % (r0 + t["shift_ratio_K100_to_inf"])])
# The comparison with the table (Johansson, up to 1e5) is NOT written: its ratio must be recomputed first (code/table_sign_changes.json, not yet made).
W("fig4-density.dat", "label kind lo hi mid; ratio delta/(theta_1/pi); proved = PROVED (conditional), numeric = CHECKED NUMERICALLY, heuristic; table ratio not included yet", rows)
print("wrote", os.path.abspath(out))
