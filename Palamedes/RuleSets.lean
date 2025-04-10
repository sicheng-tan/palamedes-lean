import Aesop

declare_aesop_rule_sets [palamedes]

initialize do
  let _ ← Lean.Meta.registerSimpAttr `pala_simp "Test"
