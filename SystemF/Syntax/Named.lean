import SystemF.Syntax

namespace SystemF.NamedNotation

open Lean

declare_syntax_cat f_ty

syntax ident : f_ty
syntax "(" f_ty ")" : f_ty
syntax:60 f_ty:61 " → " f_ty:60 : f_ty
syntax:50 "∀ " ident ". " f_ty:50 : f_ty
syntax "#" term:max : f_ty

partial def elabTy (ctx : List Name) : TSyntax `f_ty → MacroM Term
  | `(f_ty| #$e:term) => pure e
  | `(f_ty| $x:ident) =>
    let name := x.getId.toString
    match ctx.findIdx? (· == name) with
    | some idx => `(Ty.bvar $(quote idx))
    | none => `(Ty.fvar $(quote name))
  | `(f_ty| ($T)) => elabTy ctx T
  | `(f_ty| $T₁ → $T₂) => do
    let t1 ← elabTy ctx T₁
    let t2 ← elabTy ctx T₂
    `(Ty.arr $t1 $t2)
  | `(f_ty| ∀ $X:ident. $T) => do
    let t ← elabTy (X.getId.toString :: ctx) T
    `(Ty.all $t)
  | _ => Macro.throwUnsupported


macro "[ty| " T:f_ty " ]" : term => elabTy [] T


declare_syntax_cat f_tm

syntax ident : f_tm
syntax "(" f_tm ")" : f_tm
syntax:60 f_tm:60 f_tm:61 : f_tm
syntax:70 f_tm:70 " [" f_ty "]" : f_tm
syntax:50 "λ" ident " : " f_ty ". " f_tm:50 : f_tm
syntax:50 "Λ" ident ". " f_tm:50 : f_tm
syntax "#" term:max : f_tm

partial def elabTm (ctxTy ctxTm : List Name) : TSyntax `f_tm → MacroM Term
  | `(f_tm| #$e:term) => pure e
  | `(f_tm| $x:ident) =>
    let name := x.getId.toString
    match ctxTm.findIdx? (· == name) with
    | some idx => `(Tm.bvar $(quote idx))
    | none => `(Tm.fvar $(quote name))
  | `(f_tm| ($t)) => elabTm ctxTy ctxTm t
  | `(f_tm| $t₁ $t₂) => do
    let e1 ← elabTm ctxTy ctxTm t₁
    let e2 ← elabTm ctxTy ctxTm t₂
    `(Tm.app $e1 $e2)
  | `(f_tm| $t [$T]) => do
    let e ← elabTm ctxTy ctxTm t
    let E ← elabTy ctxTy T
    `(Tm.tApp $e $E)
  | `(f_tm| λ$x:ident : $T. $t) => do
    let E ← elabTy ctxTy T
    let e ← elabTm ctxTy (x.getId.toString :: ctxTm) t
    `(Tm.lam $E $e)
  | `(f_tm| Λ$X:ident. $t) => do
    let e ← elabTm (X.getId.toString :: ctxTy) ctxTm t
    `(Tm.tLam $e)
  | _ => Macro.throwUnsupported

macro "[tm| " t:f_tm " ]" : term => elabTm [] [] t

example : [tm| Λ X. λ x : X. x] =
  Tm.tLam (Tm.lam (Ty.bvar 0) (Tm.bvar 0)) := by rfl

example (T : Ty) : [tm| λ x : #T . x] =
  Tm.lam T (Tm.bvar 0) := by rfl

end SystemF.NamedNotation
