import Lean
import Qq
import Lean4Less.PExpr
import patch.PatchTheorems

open Lean Qq

instance : Coe LocalDecl FVarId where
  coe decl := decl.fvarId

instance : ToString FVarIdSet where
toString s := toString $ s.toArray.map (·.1)

namespace Lean4Less

/--
  Optimized version of Lean.Expr.containsFVar, assuming no bound vars in `e`.
-/
def _root_.Lean.Expr.containsFVar' (e : Expr) (fv : FVarId) : Bool :=
  (e.abstract #[.fvar fv]).hasLooseBVars

def PExpr.containsFVar' (e : PExpr) (fv : LocalDecl) : Bool := -- optimized version of Lean.Expr.containsFVar
  e.toExpr.containsFVar' fv.fvarId

instance : Hashable LocalDecl where
hash l := hash (l.toExpr, l.type)

instance : BEq LocalDecl where
beq l l' := (l.toExpr, l.type) == (l'.toExpr, l'.type)

structure EContext where
  dbg : Bool := false -- (for debugging purposes)
  rev : Bool := false
  ctorStack : Array (Name × Array Name) := #[]
  reversedFvars : Std.HashSet FVarId := {}

structure LocalDeclE where
(index : Nat) (fvarId : FVarId) (userName : Name) (type : Expr) (usedLets : FVarIdSet) (value : EContext → Expr)
deriving Inhabited

inductive LocalDecl' where
| e : LocalDeclE → LocalDecl'
| l : LocalDecl → LocalDecl'
deriving Inhabited

def LocalDeclE.toLocalDecl (l : LocalDeclE) : LocalDecl :=
.ldecl l.index l.fvarId l.userName l.type (l.value {}) false default -- TODO investigate use of `LocalDeclKind` field

-- FIXME should I really be doing this?
instance : Coe (Array LocalDeclE) FVarIdSet where
coe ls := ls.foldl (init := default) fun acc l => acc.union l.usedLets

/--
Tracks fvars for an equality in both directions (useful when reversing equalities).
-/
structure FVarDataE where
A : PExpr
B : PExpr
a : PExpr
b : PExpr
u : Level
aEqb : LocalDecl
bEqa : LocalDecl
usedLets : FVarIdSet := FVarIdSet.insert default aEqb
deriving Inhabited

structure LVarDataE where
A : PExpr
B : PExpr
a : PExpr
b : PExpr
u : Level
v : FVarId
usedLets : FVarIdSet := FVarIdSet.insert default v
deriving Inhabited

structure FVarData where
aEqb : LocalDecl
bEqa : LocalDecl
lets : Array LocalDeclE
usedLets : FVarIdSet := lets
deriving Inhabited

structure SorryData where
u    : Level
A    : PExpr
a    : PExpr
B    : PExpr
b    : PExpr
deriving Inhabited, Hashable, BEq

structure CastData (EExpr : Type) where
u    : Level
A    : PExpr
B    : PExpr
e    : PExpr
p    : EExpr
deriving Inhabited, Hashable, BEq



structure LamABData (EExpr : Type) where
B      : PExpr
b      : LocalDecl
blets  : Array LocalDeclE
vaEqb  : FVarData
hAB    : EExpr × FVarIdSet
usedLets : FVarIdSet := hAB.2.union (blets : FVarIdSet) |>.union vaEqb.usedLets

structure LamUVData where
V   : PExpr × LocalDecl
deriving Hashable, BEq

inductive LamDataExtra (EExpr : Type) where
| ABUV : LamABData EExpr → LamUVData → LamDataExtra EExpr
| UV   : LamUVData → LamDataExtra EExpr
| none : LamDataExtra EExpr
with
@[computed_field]
usedLets : (EExpr : Type) → LamDataExtra EExpr → FVarIdSet
| _, .ABUV d .. => d.usedLets
| _, _ => default
deriving Inhabited

/--
  Stores the information needed to prove that
  `(fun a => f a) ≍ (fun b => g b)` for two functions `f` and `g`.

  This information is used by `LamData.toExpr` to produce the heq proof term
  with the patch theorems `L4L.lambdaHEq`, `L4L.lambdaHEqABUV`, etc.

-/
structure LamData (EExpr : Type) where
u      : Level
v      : Level
/-- `A : Sort u`. This is the domain of the two functions. -/
A      : PExpr
/-- `U : Sort v` or `U : A → Sort v`. This is the codomain of the two functions. -/
U      : PExpr × LocalDecl
/-- `f : A → U` or `f : (a : A) → U a`. This one of the two functions. -/
f      : PExpr
/-- The local term of type `A` (appears in the types of `f` and `g`) -/
a      : LocalDecl
alets  : Array LocalDeclE
/-- `g : A → U` or `g : (a : A) → U a`. This is one of the two functions. -/
g      : PExpr
faEqgx : EExpr × FVarIdSet
extra  : LamDataExtra EExpr := .none
usedLets := faEqgx.2.union extra.usedLets |>.union (alets : FVarIdSet)
deriving Inhabited


structure ForallUVData (EExpr : Type) where
V      : PExpr × LocalDecl
UaEqVx : EExpr × FVarIdSet
usedLets := UaEqVx.2
deriving Inhabited

structure ForallABUVData (EExpr : Type) where
B      : PExpr
b      : LocalDecl
blets  : Array LocalDeclE
vaEqb  : FVarData
hAB    : EExpr × FVarIdSet
V      : PExpr × LocalDecl
UaEqVx : EExpr × FVarIdSet
usedLets := hAB.2.union UaEqVx.2 |>.union (blets : FVarIdSet) |>.union vaEqb.usedLets

structure ForallABData (EExpr : Type) where
B      : PExpr
b      : LocalDecl
blets  : Array LocalDeclE
vaEqb  : FVarData
hAB    : EExpr × FVarIdSet
usedLets := hAB.2.union (blets : FVarIdSet) |>.union vaEqb.usedLets

-- structure ForallABUVAppData (EExpr : Type) :=
-- b      : LocalDecl
-- vaEqb  : FVarData
-- V      : PExpr × LocalDecl
-- UaEqVx : EExpr
-- deriving Hashable, BEq

-- structure ForallABAppData (EExpr : Type) :=
-- b      : LocalDecl
-- vaEqb  : FVarData
-- deriving Hashable, BEq

inductive ForallDataExtra (EExpr : Type) where
| ABUV   : ForallABUVData EExpr → ForallDataExtra EExpr
| UV     : ForallUVData EExpr → ForallDataExtra EExpr
| AB     : ForallABData EExpr → ForallDataExtra EExpr
with
@[computed_field]
usedLets : (EExpr : Type) → ForallDataExtra EExpr → FVarIdSet
| _, .ABUV d ..
| _, .UV d ..
| _, .AB d .. => d.usedLets
deriving Inhabited

structure ForallData (EExpr : Type) where
u      : Level
v      : Level
A      : PExpr
a      : LocalDecl
alets  : Array LocalDeclE
U      : PExpr × LocalDecl
extra  : ForallDataExtra EExpr
usedLets : FVarIdSet := .union extra.usedLets (alets : FVarIdSet)
deriving Inhabited



structure HUVDataExtra where
b      : LocalDecl
blets  : Array LocalDeclE
vaEqb  : FVarData
usedLets : FVarIdSet := .union (blets : FVarIdSet) vaEqb.usedLets
deriving Inhabited

structure HUVData (EExpr : Type) where
a      : LocalDecl
alets  : Array LocalDeclE
UaEqVb : EExpr × FVarIdSet
extra  : Option HUVDataExtra
usedLets := UaEqVb.2.union (alets : FVarIdSet) |>.union $ (extra.map fun d => d.usedLets).getD default
deriving Inhabited



structure AppDataNone (EExpr : Type) where
g    : PExpr
fEqg : EExpr × FVarIdSet
b    : PExpr
aEqb : EExpr × FVarIdSet
usedLets := fEqg.2.union aEqb.2
deriving Inhabited

structure AppDataArg (EExpr : Type) where
b    : PExpr
aEqb : EExpr × FVarIdSet
usedLets := aEqb.2
deriving Inhabited

structure AppDataFun (EExpr : Type) where
g    : PExpr
fEqg : EExpr × FVarIdSet
usedLets := fEqg.2
deriving Inhabited

structure AppDataAB (EExpr : Type) where
B    : PExpr
hAB  : EExpr × FVarIdSet
g    : PExpr
fEqg : EExpr × FVarIdSet
b    : PExpr
aEqb : EExpr × FVarIdSet
usedLets := hAB.2.union fEqg.2 |>.union aEqb.2
deriving Inhabited

structure AppDataUV (EExpr : Type) where
V    : PExpr × LocalDecl
hUV  : HUVData EExpr
g    : PExpr
fEqg : EExpr × FVarIdSet
b    : PExpr
aEqb : EExpr × FVarIdSet
usedLets := fEqg.2.union aEqb.2 |>.union hUV.usedLets
deriving Inhabited

structure AppDataUVFun (EExpr : Type) where
V    : PExpr × LocalDecl
hUV  : HUVData EExpr
g    : PExpr
fEqg : EExpr × FVarIdSet
usedLets := fEqg.2.union hUV.usedLets
deriving Inhabited

structure AppDataABUV (EExpr : Type) where
B    : PExpr
hAB  : EExpr × FVarIdSet
V    : PExpr × LocalDecl
hUV  : HUVData EExpr
g    : PExpr
fEqg : EExpr × FVarIdSet
b    : PExpr
aEqb : EExpr × FVarIdSet
usedLets := fEqg.2.union hUV.usedLets |>.union aEqb.2 |>.union hAB.2
deriving Inhabited

inductive AppDataExtra (EExpr : Type) where
| none  : AppDataNone EExpr → AppDataExtra EExpr
| Fun   : AppDataFun EExpr → AppDataExtra EExpr
| Arg   : AppDataArg EExpr → AppDataExtra EExpr
| UV    : AppDataUV EExpr → AppDataExtra EExpr
| UVFun : AppDataUVFun EExpr → AppDataExtra EExpr
| AB    : AppDataAB EExpr → AppDataExtra EExpr
| ABUV  : AppDataABUV EExpr → AppDataExtra EExpr
with
@[computed_field]
usedLets : (EExpr : Type) → AppDataExtra EExpr → FVarIdSet
| _, .none  d
| _, .Fun   d
| _, .Arg   d
| _, .UV    d
| _, .UVFun d
| _, .AB    d
| _, .ABUV  d => d.usedLets
deriving Inhabited

structure AppData (EExpr : Type) where
u     : Level
v     : Level
A     : PExpr
U     : PExpr × LocalDecl -- TODO mae fvar arg optional
f     : PExpr
a     : PExpr
extra : AppDataExtra EExpr
usedLets' : FVarIdSet := default
usedLets := usedLets'.union extra.usedLets
deriving Inhabited



structure TransData (EExpr : Type) where
u     : Level
A     : PExpr
B     : PExpr
C     : PExpr
a     : PExpr
b     : PExpr
c     : PExpr
aEqb  : EExpr × FVarIdSet
bEqc  : EExpr × FVarIdSet
usedLets := aEqb.2.union bEqc.2
deriving Inhabited



-- structure SymmData (EExpr : Type) where
-- u     : Level
-- A     : PExpr
-- B     : PExpr
-- a     : PExpr
-- b     : PExpr
-- aEqb  : EExpr
-- deriving Inhabited, Hashable, BEq
--


structure ReflData where
u     : Level
A     : PExpr
a     : PExpr
deriving Inhabited



structure PIDataHEq (EExpr : Type) where
Q    : PExpr
hPQ  : EExpr × FVarIdSet
usedLets := hPQ.2
deriving Inhabited

inductive PIDataExtra (EExpr : Type) where
| none
| HEq   : PIDataHEq EExpr → PIDataExtra EExpr
with
@[computed_field]
usedLets : (EExpr : Type) → PIDataExtra EExpr → FVarIdSet
| _, .HEq d .. => d.usedLets
| _, _ => default
deriving Inhabited

structure PIData (EExpr : Type) where
P     : PExpr
p     : PExpr
q     : PExpr
extra : PIDataExtra EExpr := .none
usedLets := extra.usedLets
deriving Inhabited

/--
  Tracks the data needed to create a proof
  that an applied recursor is equal to its iota reduction.
-/
structure IotaData where
  levels : List Level
  recArgs : Array Expr
  majorArgs : Array Expr
  reductionThm : Name

/--
Structured data representing expressions for proofs of equality.
-/
inductive EExpr where
| lam      : LamData EExpr → EExpr
| forallE  : ForallData EExpr → EExpr
| app      : AppData EExpr → EExpr
| trans    : TransData EExpr → EExpr
-- | symm     : SymmData EExpr → EExpr
| refl     : ReflData → EExpr
| fvar     : FVarDataE → EExpr
| lvar     : LVarDataE → EExpr
| prfIrrel : PIData EExpr → EExpr
| sry      : SorryData → EExpr
| cast     : CastData EExpr → EExpr
| rev      : EExpr → EExpr -- "thunked" equality reversal
| iota     : IotaData → EExpr
with
  @[computed_field]
  usedLets : @& EExpr → FVarIdSet
  | .lam d
  | .forallE d
  | .app d
  | .trans d
  | .prfIrrel d
  | .rev d
  | .fvar d
  | .lvar d => d.usedLets
  | .refl _ => default
  | .sry _  => default
  | .cast _ => default
  | .iota _ => default
deriving Inhabited

instance : Coe EExpr (EExpr × FVarIdSet) where
coe e := (e, e.usedLets)

instance : Coe (EExpr × FVarIdSet) EExpr where
coe p := p.1

structure EState where -- TODO why is this needed for dbg_trace to show up?
  -- toExprCache : Std.HashMap EExpr Expr := {}
  -- reverseCache : Std.HashMap EExpr EExpr := {}

abbrev EM := ReaderT EContext <| StateT EState <| Id

def EM.run (dbg : Bool := false) (x : EM α) : α :=
  (StateT.run (x { dbg }) {}).1

def EM.run' (ctx : EContext) (x : EM α) : α :=
  (StateT.run (x ctx) {}).1

def withRev (rev : Bool) (x : EM α) : EM α :=
  withReader (fun ctx => {ctx with rev}) x

def withReversedFVar (d : FVarId) (x : EM α) : EM α :=
  withReader (fun ctx => {ctx with reversedFvars := ctx.reversedFvars.insert d}) x

def withReversedFVars (ds : Array FVarId) (x : EM α) : EM α :=
  withReader (fun ctx => {ctx with reversedFvars := ds.foldl (init := ctx.reversedFvars) fun acc d => acc.insert d}) x

def swapRev (x : EM α) : EM α :=
  withReader (fun ctx => {ctx with rev := not ctx.rev}) x

def rev : EM Bool := do pure (← read).rev

abbrev ttrace (msg : String) : EM Unit := do
  if (← read).dbg then
    dbg_trace msg


def PExpr.replaceFVar (e fvar val : PExpr) : PExpr := e.toExpr.replaceFVar fvar val |>.toPExpr

def _root_.Lean.LocalDecl.replaceFVar (fvar val : PExpr) (var : LocalDecl) : LocalDecl :=
  assert! not (var.fvarId == fvar.toExpr.fvarId!)
  var.replaceFVarId fvar.toExpr.fvarId! val

def expandLets' (lets : Array LocalDeclE) (e : Expr) : EM Expr := do
  let mut newLets := #[]
  let mut prevLetVars := #[]
  for l in lets do
    newLets := newLets.push $ (l.value (← read)).replaceFVars prevLetVars newLets
    prevLetVars := prevLetVars.push (.fvar l.fvarId)
  let ret := e.replaceFVars prevLetVars newLets
  pure ret

def expandLets (lets : Array LocalDecl) (e : Expr) : Expr := Id.run $ do
  let ret := (expandLets' (lets.map fun l => .mk l.index l.fvarId l.userName l.type default (fun _ => l.value)) e).run
  pure ret

def expandLetsForall (lctx : LocalContext) (fvars : Array Expr) (lets : Array (Array LocalDecl)) (e : Expr) : Expr := Id.run $ do
  let mut ret := e
  for (fv, ls) in fvars.zip lets |>.reverse do
    ret := lctx.mkForall #[fv] (expandLets ls ret) |>.toPExpr
  pure ret

def expandLetsLambda (lctx : LocalContext) (fvars : Array Expr) (lets : Array (Array LocalDecl)) (e : Expr) : Expr := Id.run $ do
  let mut ret := e
  for (fv, ls) in fvars.zip lets |>.reverse do
    ret := lctx.mkLambda #[fv] (expandLets ls ret) |>.toPExpr
  pure ret
  -- (expandLets' lets e).run {}

def mkLambda (vars : Array LocalDecl) (b : Expr) : EM PExpr := do
  pure $ LocalContext.mkLambda (vars.foldl (init := default) fun lctx decl => lctx.addDecl decl) (vars.map (·.toExpr)) b |>.toPExpr

def mkForall (vars : Array LocalDecl) (b : Expr) : PExpr := LocalContext.mkForall (vars.foldl (init := default) fun lctx decl => lctx.addDecl decl) (vars.map (·.toExpr)) b |>.toPExpr

def getMaybeDepLemmaApp (Uas : Array PExpr) (as : Array LocalDecl) : EM $ Array PExpr × Bool := do
  let dep := Uas.zip as |>.foldl (init := false) fun acc (Ua, a) =>
    Ua.toExpr.containsFVar' a.fvarId || acc
  let ret ← Uas.zip as |>.mapM fun (Ua, a) => do
    if dep then
      mkLambda #[a] Ua
    else
      pure Ua
  pure (ret, dep)

def getMaybeDepLemmaApp1 (U : PExpr × LocalDecl) : EM (PExpr × Bool) := do
  let (Ua, a) := U
  match ← getMaybeDepLemmaApp #[Ua] #[a] with
  | (#[U], dep) => pure (U, dep)
  | _ => unreachable!

def getMaybeDepLemmaApp2 (U V : (PExpr × LocalDecl)) : EM (PExpr × PExpr × Bool) := do
  let (Ua, a) := U
  let (Vb, b) := V
  match ← getMaybeDepLemmaApp #[Ua, Vb] #[a, b] with
  | (#[U, V], dep) => pure (U, V, dep)
  | _ => unreachable!

mutual
def HUVData.toExprDep' (e : HUVData EExpr) : EM Expr := match e with -- FIXME why can't I use a single function here?
| {a, UaEqVb, extra, alets, ..} => do
  let ret ← if (← rev) then withReversedFVars (alets.map (·.fvarId)) do
    match extra with
      | .some {b, vaEqb, blets, ..} => withReversedFVars (#[vaEqb.aEqb.fvarId] ++ blets.map (·.fvarId) ++ vaEqb.lets.map (·.fvarId)) do
        let h ← expandLets' (alets ++ blets ++ vaEqb.lets) (← UaEqVb.1.toExpr')
        -- mkLambda (← expandLets #[(b, blets), (a, alets), (vaEqb.bEqa, vaEqb.lets)]) (← UaEqVb.1.toExpr') -- TODO fix let variable ordering (should be same as context order)
        mkLambda #[b, a, vaEqb.bEqa] h
      | .none =>
        let h ← expandLets' alets (← UaEqVb.1.toExpr')
        mkLambda #[a] h
  else
    match extra with
      | .some {b, vaEqb, blets, ..} =>
        let h ← expandLets' (alets ++ blets ++ vaEqb.lets) (← UaEqVb.1.toExpr')
        mkLambda #[a, b, vaEqb.aEqb] h
      | .none =>
        let h ← expandLets' alets (← UaEqVb.1.toExpr')
        mkLambda #[a] h
  pure ret

def HUVData.toExpr' (e : HUVData EExpr) : EM Expr := match e with
| {UaEqVb, ..} => do
  pure (← UaEqVb.1.toExpr')

def LamDataExtra.lemmaName (dep : Bool) (d : LamDataExtra EExpr) : Name :=
let name := match d with
| .ABUV .. => `L4L.lambdaHEqABUV
| .UV .. => `L4L.lambdaHEqUV
| .none => `L4L.lambdaHEq
if dep then name.toString ++ "'" |>.toName else name

def dbgFIds := #["_kernel_fresh.3032".toName, "_kernel_fresh.3036".toName, "_kernel_fresh.910".toName, "_kernel_fresh.914".toName]

def LamData.toExpr (e : LamData EExpr) : EM Expr := match e with
| {u, v, A, U, f, a, g, faEqgx, extra, alets, ..} => do
  if (← rev) then withReversedFVars (alets.map (·.fvarId)) do
    let hfg ← match extra with
    | .ABUV {b, vaEqb, blets, ..} .. => withReversedFVars (#[vaEqb.aEqb.fvarId] ++ blets.map (·.fvarId) ++ vaEqb.lets.map (·.fvarId)) do
      let h ← expandLets' (alets ++ blets ++ vaEqb.lets) (← faEqgx.1.toExpr')
      mkLambda #[b, a, vaEqb.bEqa] h
    | .UV ..
    | .none =>
      let h ← expandLets' alets (← faEqgx.1.toExpr')
      mkLambda #[a] h

    let (args, dep) ← match extra with
    | .ABUV {B, hAB, ..} {V} =>
        let (U, V, dep) ← getMaybeDepLemmaApp2 U V
        pure $ (#[B.toExpr, A, V, U, g, f, (← hAB.1.toExpr'), hfg], dep)
    | .UV {V} =>
        let (U, V, dep) ← getMaybeDepLemmaApp2 U V
        pure (#[A.toExpr, V, U, g, f, hfg], dep)
    | .none =>
        let (U, dep) ← getMaybeDepLemmaApp1 U
        pure (#[A.toExpr, U, g, f, hfg], dep)
    let n := extra.lemmaName dep
    pure $ Lean.mkAppN (.const n [u, v]) args
  else
    let hfg ← match extra with
    | .ABUV {b, vaEqb, blets, ..} .. =>
      let h ← expandLets' (alets ++ blets ++ vaEqb.lets) (← faEqgx.1.toExpr')
      mkLambda #[a, b, vaEqb.aEqb] h
    | .UV ..
    | .none =>
      let h ← expandLets' alets (← faEqgx.1.toExpr')
      mkLambda #[a] h

    let (args, dep, _U) ← match extra with
    | .ABUV {B, hAB, ..} {V} =>
        let (U, V, dep) ← getMaybeDepLemmaApp2 U V
        -- if dbgFIds.any (· == a.fvarId.name) then
        --   dbg_trace s!"DBG[0]: {a.fvarId.name}, {b.fvarId.name}, {dep}, {Lean.collectFVars default V |>.fvarIds.map (·.name)}"
        pure $ (#[A.toExpr, B, U, V, f, g, (← hAB.1.toExpr'), hfg], dep, V)
    | .UV {V} =>
        let (U, V, dep) ← getMaybeDepLemmaApp2 U V
        pure (#[A.toExpr, U, V, f, g, hfg], dep, U)
    | .none =>
        let (U, dep) ← getMaybeDepLemmaApp1 U
        pure (#[A.toExpr, U, f, g, hfg], dep, U)

    let n := extra.lemmaName dep
    pure $ Lean.mkAppN (.const n [u, v]) args

def ForallDataExtra.lemmaName (dep : Bool) (d : ForallDataExtra EExpr) : Name :=
let name := match d with
| .ABUV .. => `L4L.forallHEqABUV
| .AB .. => `L4L.forallHEqAB
| .UV .. => `L4L.forallHEqUV
if dep then name.toString ++ "'" |>.toName else name

def ForallData.toExpr (e : ForallData EExpr) : EM Expr := match e with
| {u, v, A, U, a, extra, alets, ..} => do

  let (U, V?, dep) ← do
    match extra with
    | .ABUV {V, ..}
    | .UV {V, ..} =>
      let (U, V, dep) ← getMaybeDepLemmaApp2 U V
      pure (U, V, dep)
    | .AB {..} =>
      let (U, dep) ← getMaybeDepLemmaApp1 U
      assert! not dep
      pure (U, default, dep)

  let (args, dep) ← if (← rev) then
    let hUV dep := do withReversedFVars (alets.map (·.fvarId)) do
      if dep then
        match extra with
        | .ABUV {b, vaEqb, UaEqVx, blets, ..} => withReversedFVars (#[vaEqb.aEqb.fvarId] ++ blets.map (·.fvarId) ++ vaEqb.lets.map (·.fvarId)) do
          let h ← expandLets' (alets ++ blets ++ vaEqb.lets) (← UaEqVx.1.toExpr')
          -- mkLambda (← expandLets #[(b, blets), (a, alets), (vaEqb.bEqa, vaEqb.lets)]) (← UaEqVb.1.toExpr') -- TODO fix let variable ordering (should be same as context order)
          mkLambda #[b, a, vaEqb.bEqa] h
        | .UV {UaEqVx, ..} =>
          let h ← expandLets' alets (← UaEqVx.1.toExpr')
          mkLambda #[a] h
        | _ => unreachable!
      else
        match extra with
        | .ABUV {UaEqVx, ..} =>
          pure $ ← expandLets' alets (← UaEqVx.1.toExpr').toPExpr
        | .UV {UaEqVx, ..} =>
          pure $ ← expandLets' alets (← UaEqVx.1.toExpr').toPExpr
        | _ => unreachable!

    match extra with
    | .ABUV {B, hAB, ..} =>
      pure $ (#[B.toExpr, A, V?, U, (← hAB.1.toExpr'), (← hUV dep)], dep)
    | .UV .. =>
      pure (#[A.toExpr, V?, U, (← hUV dep)], dep)
    | .AB {B, hAB, ..} =>
      pure (#[B.toExpr, A.toExpr, U, (← hAB.1.toExpr')], dep)
  else
    let hUV dep := do
      if dep then
        match extra with
        | .ABUV {b, vaEqb, UaEqVx, blets, ..} =>
          let h ← expandLets' (alets ++ blets ++ vaEqb.lets) (← UaEqVx.1.toExpr')
          mkLambda #[a, b, vaEqb.aEqb] h
        | .UV {UaEqVx, ..} =>
          let h ← expandLets' alets (← UaEqVx.1.toExpr')
          mkLambda #[a] h
        | _ => unreachable!
      else
        match extra with
        | .ABUV {UaEqVx, ..} =>
          pure $ ← expandLets' alets (← UaEqVx.1.toExpr').toPExpr
        | .UV {UaEqVx, ..} =>
          pure $ ← expandLets' alets (← UaEqVx.1.toExpr').toPExpr
        | _ => unreachable!

    match extra with
    | .ABUV {B, hAB, ..} =>
      pure $ (#[A.toExpr, B, U, V?, (← hAB.1.toExpr'), (← hUV dep)], dep)
    | .UV .. =>
      pure (#[A.toExpr, U, V?, (← hUV dep)], dep)
    | .AB {B, hAB, ..} =>
      pure (#[A.toExpr, B.toExpr, U, (← hAB.1.toExpr')], dep)

  let n := extra.lemmaName dep
  pure $ Lean.mkAppN (.const n [u, v]) args

def AppDataExtra.lemmaName (dep : Bool) (d : AppDataExtra EExpr) : Name :=
let name := match d with
| .ABUV .. => `L4L.appHEqABUV
| .UV .. => `L4L.appHEqUV
| .UVFun .. => `L4L.appFunHEqUV
| .AB .. => `L4L.appHEqAB
| .none .. => `L4L.appHEq
| .Arg .. => `L4L.appArgHEq
| .Fun .. => `L4L.appFunHEq
if dep then name.toString ++ "'" |>.toName else name

def AppData.toExpr (e : AppData EExpr) : EM Expr := match e with
| {u, v, A, U, f, a, extra, ..} => do
  let (args, dep) ← if (← rev) then
    match extra with
    | .ABUV {B, hAB, V, hUV, g, fEqg, b, aEqb, ..} =>
      let (U, V, dep) ← getMaybeDepLemmaApp2 U V
      pure (#[B.toExpr, A, V, U, (← hAB.1.toExpr'), (← if dep then do hUV.toExprDep' else hUV.toExpr'), g, f, b, a, (← fEqg.1.toExpr'), (← aEqb.1.toExpr')], dep)
    | .UV {V, hUV, g, fEqg, b, aEqb, ..} =>
      let (U, V, dep) ← getMaybeDepLemmaApp2 U V
      pure (#[A.toExpr, V, U, (← if dep then hUV.toExprDep' else hUV.toExpr'), g, f, b, a, (← fEqg.1.toExpr'), (← aEqb.1.toExpr')], dep)
    | .UVFun {V, hUV, g, fEqg, ..} =>
      let (U, V, dep) ← getMaybeDepLemmaApp2 U V
      pure (#[A.toExpr, V, U, (← if dep then hUV.toExprDep' else hUV.toExpr'), g, f, a, (← fEqg.1.toExpr')], dep)
    | .AB {B, hAB, g, fEqg, b, aEqb, ..} =>
      let U := U.1
      pure (#[B.toExpr, A, U, (← hAB.1.toExpr'), g, f, b, a, (← fEqg.1.toExpr'), (← aEqb.1.toExpr')], false)
    | .none {g, fEqg, b, aEqb, ..} => -- TODO fails to show termination if doing nested match?
      let (U, dep) ← getMaybeDepLemmaApp1 U
      pure (#[A.toExpr, U, g, f, b, a, (← fEqg.1.toExpr'), (← aEqb.1.toExpr')], dep)
    | .Fun {g, fEqg, ..} =>
      let (U, dep) ← getMaybeDepLemmaApp1 U
      pure (#[A.toExpr, U, g, f, a, (← fEqg.1.toExpr')], dep)
    | .Arg {b, aEqb, ..} =>
      let (U, dep) ← getMaybeDepLemmaApp1 U
      pure (#[A.toExpr, U, f, b, a, (← aEqb.1.toExpr')], dep)
  else
    match extra with
    | .ABUV {B, hAB, V, hUV, g, fEqg, b, aEqb, ..} =>
      let (U, V, dep) ← getMaybeDepLemmaApp2 U V
      pure (#[A.toExpr, B, U, V, (← hAB.1.toExpr'), (← if dep then do hUV.toExprDep' else hUV.toExpr'), f, g, a, b, (← fEqg.1.toExpr'), (← aEqb.1.toExpr')], dep)
    | .UV {V, hUV, g, fEqg, b, aEqb, ..} =>
      let (U, V, dep) ← getMaybeDepLemmaApp2 U V
      pure (#[A.toExpr, U, V, (← if dep then hUV.toExprDep' else hUV.toExpr'), f, g, a, b, (← fEqg.1.toExpr'), (← aEqb.1.toExpr')], dep)
    | .UVFun {V, hUV, g, fEqg, ..} =>
      let (U, V, dep) ← getMaybeDepLemmaApp2 U V
      pure (#[A.toExpr, U, V, (← if dep then hUV.toExprDep' else hUV.toExpr'), f, g, a, (← fEqg.1.toExpr')], dep)
    | .AB {B, hAB, g, fEqg, b, aEqb, ..} =>
      let U := U.1
      pure (#[A.toExpr, B, U, (← hAB.1.toExpr'), f, g, a, b, (← fEqg.1.toExpr'), (← aEqb.1.toExpr')], false)
    | .none {g, fEqg, b, aEqb, ..} => -- TODO fails to show termination if doing nested match?
      let (U, dep) ← getMaybeDepLemmaApp1 U
      pure (#[A.toExpr, U, f, g, a, b, (← fEqg.1.toExpr'), (← aEqb.1.toExpr')], dep)
    | .Fun {g, fEqg, ..} =>
      let (U, dep) ← getMaybeDepLemmaApp1 U
      pure (#[A.toExpr, U, f, g, a, (← fEqg.1.toExpr')], dep)
    | .Arg {b, aEqb, ..} =>
      let (U, dep) ← getMaybeDepLemmaApp1 U
      pure (#[A.toExpr, U, f, a, b, (← aEqb.1.toExpr')], dep)
  let n := extra.lemmaName dep
  pure $ Lean.mkAppN (.const n [u, v]) args

def TransData.toExpr (e : TransData EExpr) : EM Expr := match e with
| {u, A, B, C, a, b, c, aEqb, bEqc, ..} => do
  if (← rev) then
    pure $ Lean.mkAppN (.const `HEq.trans [u]) #[C, B, A, c, b, a, (← bEqc.1.toExpr'), (← aEqb.1.toExpr') ]
  else
    pure $ Lean.mkAppN (.const `HEq.trans [u]) #[A, B, C, a, b, c, (← aEqb.1.toExpr'), (← bEqc.1.toExpr')]

-- def SymmData.toExpr (e : SymmData EExpr) : EM Expr := do match e with
-- | {u, A, B, a, b, aEqb} =>
--   if (← rev) then
--     swapRev aEqb.toExpr'
--   else
--     pure $ Lean.mkAppN (.const `HEq.symm [u]) #[A, B, a, b, (← aEqb.toExpr')]

def ReflData.toExpr : ReflData → EM Expr
| {u, A, a} => pure $ Lean.mkAppN (.const `L4L.HEqRefl [u]) #[A, a]

def PIData.toExpr (e : PIData EExpr) : EM Expr := match e with
| {P, p, q, extra, ..} => do
  if (← rev) then
    match extra with
    | .none =>
      pure $ Lean.mkAppN (.const `L4L.prfIrrelHEq []) #[P, q, p]
    | .HEq {Q, hPQ, ..} =>
      pure $ Lean.mkAppN (.const `L4L.prfIrrelHEqPQ []) #[Q, P, (← hPQ.1.toExpr'), q, p]
  else
    match extra with
    | .none =>
      pure $ Lean.mkAppN (.const `L4L.prfIrrelHEq []) #[P, p, q]
    | .HEq {Q, hPQ, ..} =>
      pure $ Lean.mkAppN (.const `L4L.prfIrrelHEqPQ []) #[P, Q, (← hPQ.1.toExpr'), p, q]

def FVarDataE.toExpr : FVarDataE → EM Expr
| {aEqb, bEqa, u, A, B, a, b, ..} => do
  if (← rev) then
    if (← read).reversedFvars.contains aEqb then
      pure bEqa.toExpr
    else
      pure $ Lean.mkAppN (.const `HEq.symm [u]) #[A, B, a, b, aEqb.toExpr]
  else
    if (← read).reversedFvars.contains aEqb then
      pure $ Lean.mkAppN (.const `HEq.symm [u]) #[B, A, b, a, bEqa.toExpr]
    else
      pure aEqb.toExpr

def LVarDataE.toExpr : LVarDataE → EM Expr
| ({v, u, A, B, a, b, ..}) => do
  if (← rev) then
    if (← read).reversedFvars.contains v then
      pure $ .fvar v
    else
      pure $ Lean.mkAppN (.const `HEq.symm [u]) #[A, B, a, b, .fvar v]
  else
    if (← read).reversedFvars.contains v then
      pure $ Lean.mkAppN (.const `HEq.symm [u]) #[B, A, b, a, .fvar v]
    else
      pure $ .fvar v

def SorryData.toExpr : SorryData → EM Expr
| {u, A, a, B, b} => do
  if (← rev) then
    pure $ Lean.mkAppN (.const `sorryAx [0]) #[Lean.mkAppN (.const ``HEq [u]) #[B, b, A, a], .const `Bool.false []]
  else
    pure $ Lean.mkAppN (.const `sorryAx [0]) #[Lean.mkAppN (.const ``HEq [u]) #[A, a, B, b], .const `Bool.false []]

def CastData.toExpr : CastData EExpr → EM Expr
| {u, A, B, e, p} => do
  if (← rev) then
    pure $ Lean.mkAppN (.const `L4L.castOrigHEqSymm [u]) #[A, B, ← (swapRev p.toExpr'),  e]
  else
    pure $ Lean.mkAppN (.const `L4L.castOrigHEq [u]) #[A, B, ← p.toExpr',  e]

/--
  Convert the data representing the proof of an iota reduction
  into an actual proof of an iota reduction.
-/
def IotaData.toExpr : IotaData → EM Expr
| {levels, recArgs, majorArgs, reductionThm} =>
  pure <| mkAppN (mkConst reductionThm levels) (recArgs ++ majorArgs)

def EExpr.ctorName : EExpr → Name
  | .lam .. => `lam
  | .forallE .. => `forallE
  | .app .. => `app
  | .fvar .. => `fvar
  | .lvar .. => `lvar
  | .trans .. => `trans
  | .refl .. => `refl
  | .prfIrrel .. => `prfIrrel
  | .sry .. => `sry
  | .cast .. => `cast
  | .rev .. => `rev
  | .iota .. => `iota

def withCtorName (n : Name × Array Name) (m : EM T) : EM T := do
  withReader (fun ctx => {ctx with ctorStack := ctx.ctorStack.push n}) m

def EExpr.toExpr' (e : EExpr) : EM Expr :=
  withCtorName (e.ctorName, e.usedLets.toArray.map (·.name)) do
  let ret ← match e with
  | .lam d
  | .forallE d
  | .app d
  | .fvar d
  | .lvar d
  | .trans d
  | .refl d
  | .prfIrrel d
  | .sry d
  | .iota d
  | .cast d => d.toExpr
  | .rev e => do
    let ret ← (swapRev e.toExpr')
    pure ret
  pure ret

-- def EExpr.toSorry (e : EExpr) : EExpr :=
--   match e with
--   | .other l T S t s _ => .sry {u := l, A := T, B := S, a := t, b := s}
--   | .lam d => .sry {u := .ima, A := T, B := S, a := t, b := s}
--   | .forallE d
--   | .app d
--   | .fvar d
--   | .trans d
--   -- | .symm d
--   | .refl d
--   | .prfIrrel d
--   | .sry d  => d.toExpr
--   -- | .rev .. => panic! "encountered thunked reversal"
--   | .rev e => sorry


end

def EExpr.toExpr (e : EExpr) (dbg := false) : Expr := Id.run $ do
  -- dbg_trace s!"DBG[1]: EExpr.lean:1066 (after def EExpr.toExpr (e : EExpr) (dbg := fal…)"
  let ret ← e.toExpr'.run dbg
  -- dbg_trace s!"DBG[2]: EExpr.lean:1068 (after let ret ← e.toExpr.run dbg)"
  pure ret

namespace EExpr

def toPExpr (e : EExpr) : PExpr := .mk e.toExpr

-- instance : BEq EExpr where
-- beq x y := x.toExpr == y.toExpr

end EExpr

instance : ToString EExpr where
toString e := toString $ e.toExpr default

-- def EExpr.instantiateRev (e : EExpr) (subst : Array EExpr) : EExpr :=
--   e.toExpr.instantiateRev (subst.map (·.toExpr)) |>.toEExpr

instance : ToString (Option EExpr) where
toString e? := toString $ e?.map (·.toExpr default)

-- instance : Coe EExpr Expr := ⟨toExpr⟩
-- instance : Coe EExpr PExpr := ⟨(EExpr.toPExpr default)⟩

structure BinderData where
name : Name
dom : PExpr
info : BinderInfo
deriving Inhabited

end Lean4Less
