"""Keep the numerical reference margin throughout the native Jacobsthal proof."""
import argparse
import hashlib
from pathlib import Path

from rejouer_borne_native_687 import between, file_text


def replace_once(source, before, after):
    if source.count(before) != 1:
        raise ValueError("Unexpected source at " + before[:70])
    return source.replace(before, after)


def pinned(root, name, digest):
    data = (root / (name + ".lean")).read_bytes()
    if hashlib.sha256(data).hexdigest() != digest:
        raise ValueError("Unexpected upstream source " + name)
    return data.decode("utf-8")


def assemble(root):
    ref = pinned(root, "Estimates/SourceRootReference",
                 "faa4adde8d1e6159ac2980bac0de65921f4fb044f9f9da986bdf2bff434aeaca")
    err = pinned(root, "Estimates/SourceRootErrorLower",
                 "965516ed90cc5464679be5a5e823d710fac0a3d9faa0151902a9f951ff017a1d")
    end = pinned(root, "Conclusions/SourceRootCompletion",
                 "d39a884155dcbb456de7cdc5192dbde7a343e84cbb1de57e4f596d18bc550fbc")
    c = "Real.exp Real.eulerMascheroniConstant"
    def track(text, name, divisor):
        return replace_once(text, "0 < " + name + " ∧", f"{name} = {c}/{divisor} ∧ 0 < {name} ∧")
    actual = between(ref, "theorem actual_source_reference_lower_bound",
                     "theorem actual_source_reference_eventually_positive")
    actual = track(actual.replace("actual_source_reference_lower_bound", "fixed_reference_bound"), "c_L", 100)
    actual = replace_once(actual, "⟨c_L,max 2 z₁,hc,", "⟨c_L,max 2 z₁,rfl,hc,")
    margin = between(ref, "theorem source_root_polynomial_margin", "theorem source_root_eventually_data")
    margin = track(margin.replace("source_root_polynomial_margin", "fixed_polynomial_margin"), "c_L", 100)
    margin = replace_once(margin, "c_L,T,hc,_hT,hMargin⟩ := actual_source_reference_lower_bound",
                          "c_L,T,eqc,hc,_hT,hMargin⟩ := fixed_reference_bound")
    margin = replace_once(margin, "⟨c_L,hc,?_⟩", "⟨c_L,eqc,hc,?_⟩")
    err = err[err.index("namespace OAI"):]
    err = track(err.replace("source_root_lower_with_stopped_correction", "fixed_stopped_correction"), "c", 200)
    err = replace_once(err, "c_L,hc_L,hRef⟩ := source_root_polynomial_margin",
                       "c_L,eqc,hc_L,hRef⟩ := fixed_polynomial_margin")
    err = replace_once(err, "⟨c_L/2,Clen,Cs,xi₀,by positivity", "⟨c_L/2,Clen,Cs,xi₀,by rw [eqc]; ring,by positivity")
    end = end[end.index("namespace OAI"):]
    end = track(end.replace("source_root_survivor_lower", "fixed_root_survivor_lower"), "c", 200)
    end = replace_once(end, "xi0,hc,hClen", "xi0,eqc,hc,hClen")
    end = replace_once(end, "source_root_lower_with_stopped_correction 1", "fixed_stopped_correction 1")
    end = replace_once(end, "⟨c,hc,?_⟩", "⟨c,eqc,hc,?_⟩")
    parts = [
        "import BorneNative687",
        "/-! An explicit logarithmic saving for Erdős 687(i). The first four proofs "
        "carry through the actual reference constant chosen in openai/math "
        "(Apache-2.0), commit adc7f1241b42e322a6451854ab7e4b4c146bf78a, "
        "in SourceRootReference, SourceRootErrorLower and SourceRootCompletion. -/",
        "open scoped Asymptotics BigOperators",
        "namespace OAI.Erdos970",
        between(ref, "namespace ErdosSourceReferenceMargin\nopen ErdosCorrectionLimit", "theorem actual_reference_limit_positive"),
        "open Filter Set\nopen scoped Topology", actual, "end ErdosSourceReferenceMargin",
        between(ref, "namespace NumberTheoryLean.SourceRootReference", "theorem source_primes_eq_root_set"),
        margin, "end NumberTheoryLean.SourceRootReference\nend OAI.Erdos970", err, end,
    ]
    interface = file_text("InterfaceSource687.lean")
    parts.extend(["namespace InterfaceSource687\nopen Filter",
                  track(between(interface, "def statement ", "end InterfaceSource687").replace(
                      "def statement ", "def fixedStatement "), "c", 200), "end InterfaceSource687"])
    producer = file_text("SourcePubliee687.lean").split("namespace SourcePubliee687",1)[1]
    producer = producer[:producer.index("#print axioms")]
    producer = producer.replace("source_bound : InterfaceSource687.statement", "fixed_bound : InterfaceSource687.fixedStatement")
    producer = replace_once(producer, "⟨c,hc,stock⟩ := Erdos970Final.source_root_survivor_lower",
                            "⟨c,eqc,hc,stock⟩ := Erdos970Final.fixed_root_survivor_lower")
    parts.extend(["namespace SourcePubliee687", replace_once(producer,"⟨c,hc,?_⟩","⟨c,eqc,hc,?_⟩"), "end SourcePubliee687"])
    src = file_text("StockSource687.lean")
    parts += ["namespace StockExplicite687\nopen Filter GainVariable687 Transfert687 StockSource687\n"
              "open OAI.Erdos970.NumberTheoryLean",
              track(between(src, "def sourceStatement ", "private theorem shift_survivors").replace(
                  "def sourceStatement ", "def fixedStatement "), "c", 200),
              between(src, "private theorem shift_survivors", "/-- A real-cutoff estimate")]
    normalized = between(src, "theorem normalize_source", "private theorem cutoff_properties")
    normalized = normalized.replace("normalize_source (h : sourceStatement)", "fixed_normalize (h : fixedStatement)")
    normalized = track(normalized, "c", 1200)
    normalized = replace_once(normalized, "⟨c,hc,hs⟩ := h", "⟨c,eqc,hc,hs⟩ := h")
    normalized = replace_once(normalized, "⟨c/6,by positivity", "⟨c/6,by rw [eqc]; ring,by positivity")
    stock = between(src, "theorem stock_of_published", "/-- The complete transfer")
    stock = stock.replace("stock_of_published (h : sourceStatement)", "fixed_stock (h : fixedStatement)")
    stock = track(stock,"c",2400)
    stock = replace_once(stock,"⟨c,hc,hs⟩ := normalize_source h","⟨c,eqc,hc,hs⟩ := fixed_normalize h")
    stock = replace_once(stock,"⟨c/2,by positivity","⟨c/2,by rw [eqc]; ring,by positivity")
    bridge = between(src,"theorem source_of_interface","theorem gain_of_interface")
    bridge = bridge.replace("source_of_interface", "fixed_bridge").replace("InterfaceSource687.statement", "InterfaceSource687.fixedStatement").replace("sourceStatement", "fixedStatement")
    parts += [normalized,between(src,"private theorem cutoff_properties","theorem stock_of_published"),stock,bridge]
    gain = file_text("GainVariable687.lean")
    parts += [between(gain,"private theorem scales","theorem reciprocal_band"),
              "open OMA.R_Erdos687_erdos_687_variants_iwaniec_R2",
              """private theorem transfer {c K d : ℝ} (hK : 0 < K) (hd : 0 < d) (hhalf : d ≤ 1/2)
    (hdel : 3*d*K < c) (stock : stockBound c d) (progression : progressionBound K d) :
    (fun x : ℕ => (Erdos687.Y x : ℝ)) =O[atTop]
      (fun x : ℕ => (x:ℝ)^2/(Real.log x)^(2+2*d)) := by""",
              "\n".join(between(gain,"  unfold stockBound at stock","/-- Uniformity concerns").splitlines())]
    # The first line of a selected proof body is stripped by between().
    parts[-1] = "  " + parts[-1]
    parts += ["""theorem explicit_gain :
    (fun x : ℕ => (Erdos687.Y x : ℝ)) =O[atTop]
      (fun x : ℕ => (x:ℝ)^2/(Real.log x)^(2+1/100000 : ℝ)) := by
  obtain ⟨c,eqc,_,hs⟩ := fixed_stock (fixed_bridge SourcePubliee687.fixed_bound)
  have margin : 3*(1/200000:ℝ)*35 < c := by
    rw [eqc]
    linarith [Real.one_half_lt_eulerMascheroniConstant, Real.add_one_le_exp Real.eulerMascheroniConstant]
  have result := transfer (by norm_num : 0 < (35:ℝ)) (by norm_num : 0 < (1/200000:ℝ))
    (by norm_num) margin (hs _ (by norm_num) (by norm_num))
    (CribleTransfert687.uniform_progression_35 (by norm_num) (by norm_num))
  convert result using 1 <;> norm_num

#print axioms explicit_gain
end StockExplicite687"""]
    return "\n\n".join(parts) + "\n"


if __name__ == "__main__":
    cli = argparse.ArgumentParser(description=__doc__)
    cli.add_argument("output", type=Path)
    cli.add_argument("--jacobsthal", type=Path, required=True)
    args = cli.parse_args()
    args.output.write_text(assemble(args.jacobsthal), encoding="utf-8", newline="\n")
