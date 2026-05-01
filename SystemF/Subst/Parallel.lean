
import SystemF.Syntax

namespace SystemF

open Notation

abbrev TySubst := Name → Ty
abbrev TmSubst := Name → Tm

def TySubst.empty : TySubst := fun X => $T X
def TmSubst.empty : TmSubst := fun x => $v x

def Ty.psubst (δ : TySubst) : Ty → Ty
  | .bvar i => .bvar i
  | .fvar X => δ X
  | .arr T₁ T₂ => .arr (T₁.psubst δ) (T₂.psubst δ)
  | .all T => .all (T.psubst δ)

def Tm.psubst (γ : TmSubst) (δ : TySubst) : Tm → Tm
  | .bvar i => .bvar i
  | .fvar x => γ x
  | .app t₁ t₂ => .app (t₁.psubst γ δ) (t₂.psubst γ δ)
  | .lam T t => .lam (T.psubst δ) (t.psubst γ δ)
  | .tApp t T => .tApp (t.psubst γ δ) (T.psubst δ)
  | .tLam t => .tLam (t.psubst γ δ)

end SystemF
