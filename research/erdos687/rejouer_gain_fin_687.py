"""Assemble the sharper interval-sieve transfer for the native source project."""
import argparse
from pathlib import Path

from rejouer_exposant_687 import assemble
from rejouer_borne_native_687 import file_text, between


def stock(jacobsthal):
    source = assemble(jacobsthal).split("private theorem scales")[0]
    source = source.replace("fixed", "sharp").replace("StockExplicite687", "StockFin687")
    source = source.replace("Constant/100", "Constant/40").replace("Constant/200", "Constant/80")
    reference = """have margin : Real.exp Real.eulerMascheroniConstant/40 <
      Real.exp Real.eulerMascheroniConstant*(-(1:ℝ)/100+2*ErdosBoundaryIntegral.signedCoefficientI/Erdos970Dependency.InvariantCostBound.costMass) := by
    have pos := Erdos970Dependency.InvariantCostBound.costMass_pos
    have ratio : (7:ℝ)/200 < 2*ErdosBoundaryIntegral.signedCoefficientI/Erdos970Dependency.InvariantCostBound.costMass := by
      apply (lt_div_iff₀ pos).2
      linarith [ErdosPositiveReference.actual_I_gt_eleven_seventyfive,ErdosPositiveReference.costMass_lt_eight]
    nlinarith [mul_pos (Real.exp_pos Real.eulerMascheroniConstant) (sub_pos.mpr ratio)]
  have hevent := actual_sourceReference_tendsto.eventually (Ioi_mem_nhds margin)"""
    source = source.replace("have hevent := actual_sourceReference_tendsto.eventually (Ioi_mem_nhds actual_reference_limit_positive)", reference)
    w = source.index("private theorem width_eventually")
    n = source.index("theorem sharp_normalize", w)
    c = source.index("private theorem cutoff_properties", n)
    q = source.index("theorem sharp_stock", c)
    width = source[w:n].replace("1/4:ℝ", "1/200:ℝ").replace("Real.log (Real.log z)/2", "99/100*Real.log (Real.log z)").replace("u/2", "99/100*u")
    norm = source[n:c].replace("Constant/1200", "Constant*33/8000").replace("c/6", "c*(33/100)")
    norm = norm.replace("(6 *", "((100/33:ℝ) *").replace("(6*", "((100/33:ℝ)*").replace("(2*Real.log w)", "((100/99)*Real.log w)")
    cut = source[c:q].replace("(Real.tendsto_log_atTop.comp ht).eventually_ge_atTop 4", "(Real.tendsto_log_atTop.comp ht).eventually_ge_atTop 100")
    cut = cut.replace("change 4 ≤ Real.log L", "change 100 ≤ Real.log L").replace("Real.log (Real.log x)/2", "(99/100)*Real.log (Real.log x)").replace("Real.log L/2", "(99/100)*Real.log L")
    tail = source[q:].replace("Constant/2400", "Constant*3267/800000").replace("⟨c/2,", "⟨c*(99/100),").replace("Real.log L/2", "(99/100)*Real.log L")
    return source[:w]+width+norm+cut+tail+"\nend StockFin687\n#print axioms StockFin687.sharp_stock\n"


def sieve():
    files = ["NormalisationSelberg687.lean", "ErreurSelberg687.lean", "CribleFin687.lean", "ProgressionFine687.lean"]
    return "import BorneNative687\n\n" + "\n\n".join(
        "\n".join(line for line in file_text(name).splitlines() if not line.startswith("import "))
        .replace("Finset.prod_le_prod (fun", "Finset.prod_le_prod₀ (fun") for name in files) + "\n"


def transfer(jacobsthal):
    src = assemble(jacobsthal)
    src = src[src.index("private theorem scales"):]
    gain = file_text("GainVariable687.lean")
    band = between(gain, "theorem reciprocal_band", "theorem block_scale")
    band = band.replace("theorem reciprocal_band", "private theorem sharp_band").replace("(hhalf : d ≤ 1/2)", "(hhalf : d ≤ 1/2) (tiny : d ≤ 1/400)")
    band = band.replace("3*d*", "(21/20)*d*").replace("20/d", "400/d").replace("20 ≤", "400 ≤")
    band = band.replace("  nlinarith only [hb, mul_le_mul_of_nonneg_right hlower hs, hlim]", """  have close : (399/400)*Real.log (x:ℝ) ≤ Real.log (top d x) := by
    rw [hlog]
    have Lp : 0 < Real.log (x:ℝ) := by change 4 ≤ Real.log (x:ℝ) at hL; linarith
    have nneg : 0 ≤ Real.log (Real.log x) := Real.log_nonneg (by change 4 ≤ Real.log (x:ℝ) at hL; linarith)
    linarith [mul_le_mul_of_nonneg_right tiny nneg,Real.log_le_sub_one_of_pos Lp]
  nlinarith only [hb,mul_le_mul_of_nonneg_right close hs,hlim]""")
    src = src.replace("open OMA.", band+"\n\nopen OMA.", 1)
    src = src.replace("(hdel : 3*d*K", "(tiny : d ≤ 1/400) (hdel : (21/20)*d*K").replace("reciprocal_band hd hhalf", "sharp_band hd hhalf tiny").replace("3*d*", "(21/20)*d*")
    src = src.replace("explicit_gain", "gain_one_two_hundred").replace("fixed_", "sharp_").replace("1/100000", "1/200").replace("1/200000", "1/400")
    src = src.replace("3*(1/400:ℝ)*35", "(21/20)*(1/400:ℝ)*(9/4)").replace("0 < (35:ℝ)", "0 < (9/4:ℝ)").replace("(by norm_num) margin", "(by norm_num) (by norm_num) margin")
    src = src.replace("CribleTransfert687.uniform_progression_35", "ProgressionFine687.uniform_progression").replace("end StockExplicite687", "end TransfertFin687")
    return ("import StockFinNatif687\nimport CribleFinNatif687\n\nnamespace TransfertFin687\n"
            "open Filter GainVariable687 Transfert687 StockFin687\nopen scoped Asymptotics BigOperators\n\n"+src)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("directory", type=Path)
    parser.add_argument("--jacobsthal", type=Path, required=True)
    args = parser.parse_args()
    for name, content in [("StockFinNatif687",stock(args.jacobsthal)), ("CribleFinNatif687",sieve()),
                          ("TransfertFinNatif687",transfer(args.jacobsthal))]:
        (args.directory / (name+".lean")).write_text(content, encoding="utf-8", newline="\n")
