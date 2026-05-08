import SystemF.Subst
import SystemF.Lc.NormAttr

namespace SystemF

open Notation

@[ln_norm_simps]
theorem substTy_refold (X : Name) (U T : Ty) :
    substTy X U T = T[X ↦ U] := rfl

@[ln_norm_simps]
theorem substTm_refold (x : Name) (u t : Tm) :
    substTm x u t = t[x ↦ u] := rfl

@[ln_norm_simps]
theorem substTmTy_refold (X : Name) (U : Ty) (t : Tm) :
    substTmTy X U t = t[X ↦ U] := rfl

end SystemF
