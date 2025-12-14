import Lean
import Lean4Less.Replay
import Lean4Lean.Util
import Lean4Lean.Commands

open Lean
open Lean4Lean

open private Lean.Kernel.Environment.add markQuotInit from Lean.Environment

def add' (env : Environment) (ci : ConstantInfo) : Environment :=
  let kenv := env.toKernelEnv
  let kenv := match ci with
    | .quotInfo _ =>
      markQuotInit kenv
    | _ => kenv
  let kenv := kenv.add ci
  updateBaseAfterKernelAdd env kenv.toMap₁

namespace Lean4Less

unsafe def withImportModuleInit (init : Environment) (mod : Name) (f : Environment → IO α) : IO α := do
  Lean.withImportModules #[{module := mod}] {} fun env => do
    let mut env := env
    for (_, c) in init.constants do
      env := add' env c
    f env

unsafe def withImportModuleAndPatchDefs (mod : Name) (f : Environment → IO α) (elabPatch := true) : IO α := do
  Lean.withImportModules #[{module := mod}] {} fun env => do
    let mut env := env
    if elabPatch then
      -- TODO how to add PatchTheorems.lean as a lake dependency?
      let .some patchEnv ← Lean.Elab.runFrontend (include_str ".." / "patch" / "PatchTheorems.lean") default default `Patch |
        throw $ IO.userError $ "elab of patching defs failed"
      for (_, c) in patchEnv.constants do
        env := add' env c
    f env

unsafe def withPatchDefs (f : Environment → IO α) : IO α := do
  let .some patchEnv ← Lean.Elab.runFrontend (include_str ".." / "patch" / "PatchTheorems.lean") default default `Patch |
    throw $ IO.userError $ "elab of patching defs failed"
  f patchEnv

def ppConst (env : Kernel.Environment) (n : Name) : IO Unit := do
  let options := default
  let options := KVMap.set options `pp.proofs true
  let options := KVMap.set options `pp.explicit true
  let options := KVMap.set options `pp.funBinderTypes true
  let some info := env.find? n | unreachable!
  try
    IO.print s!"patched {info.name}: {← (PrettyPrinter.ppExprLegacy (Environment.ofKernelEnv env) default default options info.type)}"

    match info.value? with
    | .some v =>
      if v.approxDepth < 100 then
        IO.println s!"\n{← (PrettyPrinter.ppExprLegacy (Environment.ofKernelEnv env) default default options v)}"
      else
        IO.println s!"\n [[[expression too large]]]"
    | _ => IO.println ""
  catch
  | _ =>
    IO.print s!"patched {info.name}: {info.type}"
    match info.value? with
    | .some v =>
      if v.approxDepth < 100 then
        IO.println s!"\n{v}"
      else
        IO.println s!"\n [[[expression too large]]]"
    | _ => IO.println ""

/--
The set of all constants used to patch terms, in linearised order based on
dependencies in the patched versions of their types/values.
-/
def patchConstsInitial : Array Name := #[
`L4L.prfIrrel,
`L4L.forallEqUV',
`L4L.appArgEq,
`eq_of_heq,
`cast,
`L4L.HEqRefl,
`L4L.castHEq,
`HEq,
`HEq.symm,
`HEq.refl,
`HEq.trans,
`Eq,
`Eq.refl,

`L4L.prfIrrelHEq,
`L4L.prfIrrelHEqPQ,

`L4L.forallHEqUV,
`L4L.forallHEqUV',
`L4L.forallHEqAB,
`L4L.forallHEqABUV,
`L4L.forallHEqABUV',
`L4L.appArgHEq,
`L4L.appArgHEq',
`L4L.appFunHEq,
`L4L.appFunHEq',
`L4L.appHEq,
`L4L.appHEq',
`L4L.appHEqUV,
`L4L.appHEqUV',
`L4L.appFunHEqUV,
`L4L.appFunHEqUV',
`L4L.appHEqAB,
`L4L.appHEqABUV,
`L4L.appHEqABUV',
`L4L.lambdaHEq,
`L4L.lambdaHEq',
`L4L.lambdaHEqUV,
`L4L.lambdaHEqUV',
`L4L.lambdaHEqABUV,
`L4L.lambdaHEqABUV',

`L4L.castOrigHEq,
`L4L.castOrigHEqSymm,

`L4L.appHEqBinNatFn,
-- `L4L.Nat.eq_or_lt_of_le,
`sorryAx --FIXME
]

def constsFromIotaReduction (iotaReduction : Std.HashMap Name IotaReductionData) := Id.run do
  let mut consts := []
  for (_, reductionData) in iotaReduction do
    for (_, reductionThm) in reductionData do
      consts := reductionThm :: consts
  return consts.toArray

def patchConsts (opts : TypeCheckerOpts) : Array Name :=
  (constsFromIotaReduction opts.iotaReduction) ++ patchConstsInitial

def constOverrides' : Array (Name × Name) := #[
  (`eq_of_heq, `L4L.eq_of_heq)
  -- , (`Nat.eq_or_lt_of_le, `L4L.Nat.eq_or_lt_of_le)
]

def constOverrides : Std.HashMap Name Name := constOverrides'.foldl (init := default) fun acc (n, n') => acc.insert n n'

-- def getOverrides (env : Environment) (overrides : Std.HashMap Name Name) : Std.HashMap Name ConstantInfo :=
def getOverrides (env : Kernel.Environment) : Std.HashMap Name ConstantInfo :=
  constOverrides.fold (init := default) fun acc n n' =>
    if env.constants.contains n then
      if let some ci := env.find? n' then
        acc.insert n ci
      else
        panic! s!"could not find override `{n'}` for '{n}'"
    else
      acc

def transL4L' (ns : Array Name) (env : Kernel.Environment) (pp := false) (printProgress := false) (interactive := false) (opts : TypeCheckerOpts := {}) (dbgOnly := false) : IO Environment := do
  let map := ns.foldl (init := default) fun acc n => .insert acc n
  let (_, newEnv) ← checkConstants (printErr := true) (Environment.ofKernelEnv env.toMap₁) map (@Lean4Less.addDecl (opts := opts)) (initConsts := patchConsts opts) (op := "patch") (printProgress := printProgress) (interactive := interactive) (overrides := getOverrides env) (dbgOnly := dbgOnly)
  for n in ns do
    if pp then
      ppConst newEnv.toKernelEnv n
  pure newEnv

def transL4L (n : Array Name) (env? : Option Kernel.Environment := none)
  (opts : TypeCheckerOpts := {}) : Lean.Elab.Command.CommandElabM Environment := do
  let env ← env?.getDM (do
      let e ← getEnv
      pure e.toKernelEnv
    )
  transL4L' n env (opts := opts)

def checkL4L (ns : Array Name) (env : Kernel.Environment) (printOutput := true) (printProgress := false) (interactive := false) (opts : TypeCheckerOpts := {}) (dbgOnly := false) (deps := false) : IO Environment := do
  let env ← transL4L' ns env (pp := printOutput) (printProgress := printProgress) (interactive := interactive) (opts := opts) (dbgOnly := dbgOnly)
  let env := updateBaseAfterKernelAdd env env.toKernelEnv.toMap₁
  let ns := ns
  let nSet := ns.foldl (init := default) fun acc n => acc.insert n

  let (_, checkEnv) ← checkConstants (printErr := true) env nSet Lean4Lean.addDecl (printProgress := printProgress) (opts := {proofIrrelevance := not opts.proofIrrelevance, kLikeReduction := not opts.kLikeReduction}) (interactive := interactive) (dbgOnly := false) (overrides := default) (deps := deps) (write := false)

  pure checkEnv

/--
  Remove the definitial equalities specified in `opts` from `const`.
-/
def patchConst (const : Name) (opts : TypeCheckerOpts) :
    MetaM ConstantInfo := do
  let constInfo ← getConstInfo const
  let patched := Kernel.Environment.patchDecl (← getEnv).toKernelEnv constInfo (opts := opts)
  match patched with
  | .ok res => return res
  | .error e => throwError m!"failed patching with error {e.toMessageData {}}"

open Lean.Parser.Tactic
declare_command_config_elab elabTypeCheckerOpts TypeCheckerOpts

def convertTypeCheckerOpts (opts : TypeCheckerOpts) : Lean.TypeCheckerOpts where
  proofIrrelevance := opts.proofIrrelevance
  kLikeReduction := opts.kLikeReduction
  structLikeReduction := opts.structLikeReduction
  iotaReduction := opts.iotaReduction.keys.foldl (fun acc n => acc.insert n) ∅

elab "#trans_l4l " i:ident config:optConfig : command => do
  let opts ← elabTypeCheckerOpts config
  _ ← transL4L #[i.getId] (opts := opts)

elab "#check_only " i:ident config:optConfig : command => do
  let opts := convertTypeCheckerOpts (← elabTypeCheckerOpts config)
  _ ← checkConstants (printErr := true) (← getEnv) (.insert default i.getId)
    (Lean4Lean.addDecl (verbose := true)) (opts := opts) (interactive := true)
    (overrides := getOverrides (← getEnv).toKernelEnv)

elab "#check_off " i:ident config:optConfig : command => do
  let opts := convertTypeCheckerOpts (← elabTypeCheckerOpts config)
  let opts := {opts with proofIrrelevance := false, kLikeReduction := false}
  _ ← checkConstants (printErr := true) (← getEnv) (.insert default i.getId)
    Lean4Lean.addDecl (opts := opts)
    (interactive := true) (overrides := getOverrides (← getEnv).toKernelEnv)

elab "#check_l4l" i:ident config:optConfig : command => do
  let opts ← elabTypeCheckerOpts config
  _ ← checkL4L #[i.getId] (← getEnv).toKernelEnv (interactive := true) (opts := opts)

elab "#patch_const" i:ident config:optConfig : command => do
  let opts ← elabTypeCheckerOpts config
  let res ← Elab.Command.liftTermElabM <| patchConst i.getId opts
  Lean.logInfo m!"{res.value!}"

end Lean4Less
