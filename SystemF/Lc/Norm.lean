import SystemF.Subst
import SystemF.Lc.NormAttr

namespace SystemF

open Notation

@[ln_norm_simps]
theorem Ty.subst_refold (X : Name) (U T : Ty) :
    T.subst X U = T[X ↦ U] := rfl

@[ln_norm_simps]
theorem Tm.subst_refold (x : Name) (u t : Tm) :
    t.subst x u = t[x ↦ u] := rfl

@[ln_norm_simps]
theorem Tm.substTy_refold (X : Name) (U : Ty) (t : Tm) :
    t.substTy X U = t[X ↦ U] := rfl

end SystemF
