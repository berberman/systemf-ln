import Aesop

initialize lnNormExt : Lean.Meta.SimpExtension ←
  Lean.Meta.registerSimpAttr `ln_norm_simps "Locally nameless normalization rules"

declare_aesop_rule_sets [LcRules]
