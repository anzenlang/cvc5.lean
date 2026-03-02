/-
Copyright (c) 2023-2024 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed, Adrien Champion
-/

import Lean.Elab.Command

import cvc5.Kind
import cvc5.ProofRule
import cvc5.SkolemId
import cvc5.Types



/-! # Helpers and basic definitions -/
namespace cvc5



/-! ## Errors and environment -/



/-- A kind of error. -/
inductive Error.Kind
/-- A plain error. -/
| error
/-- A recoverable error. -/
| recoverable
/-- Unsupported feature. -/
| unsupported
/-- Bad option error. -/
| option
deriving Repr

/-- Error type. -/
structure Error where mk' ::
  /-- The error message. -/
  msg : String
  /-- The error kind. -/
  (kind : Error.Kind := .error)
deriving Repr

namespace Error

/-- Error constructor. -/
def mk (msg : String) (kind : Error.Kind := .error) : Error := {msg, kind}

@[inherit_doc Kind.recoverable]
def recoverable (msg : String) : Error := mk msg .recoverable
@[inherit_doc Kind.unsupported]
def unsupported (msg : String) : Error := mk msg .unsupported
@[inherit_doc Kind.option]
def option (msg : String) : Error := mk msg .option

namespace Kind

/-- Error prefix. -/
def pref : Kind → String
  | error => ""
  | recoverable => "[recoverable] "
  | unsupported => "[unsupported] "
  | option => "[option] "

/-- String representation. -/
protected def toString (k : Kind) : String := s!"{k.pref}error"

instance : ToString Kind := ⟨Kind.toString⟩

end Kind

/-- String representation. -/
protected def toString (e : Error) : String :=
  s!"{e.kind.pref}{e.msg}"

instance : ToString Error := ⟨Error.toString⟩

/-- Panics on errors. -/
def unwrap! [Inhabited α] : Except Error α → α
  | .ok a => a
  | .error e => panic! e.toString

/-! ### Exports for the C++ layer -/

section ffi_except_constructors

/-- Only used by FFI to inject values. -/
@[export generic_except_ok]
private def mkExceptOk {α : Type} : α → Except Error α :=
  .ok

/-- Only used by FFI to inject values. -/
@[export except_ok_bool]
private def mkExceptOkBool : Bool → Except Error Bool :=
  .ok

/-- Only used by FFI to inject values. -/
@[export except_ok_u32]
private def mkExceptOkU32 : UInt32 → Except Error UInt32 :=
  .ok

/-- Only used by FFI to inject values. -/
@[export except_ok_u16]
private def mkExceptOkU16 : UInt16 → Except Error UInt16 :=
  .ok

/-- Only used by FFI to inject values. -/
@[export except_ok_u8]
private def mkExceptOkU8 : UInt8 → Except Error UInt8 :=
  .ok

/-- Only used by FFI to inject errors. -/
@[export except_err]
private def mkExceptErr {α : Type} : String → Except Error α := .error ∘ mk

end ffi_except_constructors

end Error



/-- Cvc5 environment monad transformer.

Most monadic functions in this API use the non-transformer monad `cvc5.Env`, where `m := BaseIO`.

When using an `EnvT m α`, do make sure `m` is such that `MonadLiftT BaseIO m` which gives
`MonadLiftT Env (EnvT m)`.
-/
def EnvT (m : Type → Type) (α : Type) : Type := ExceptT Error m α

/-- Cvc5 environment (`EnvT`) in `BaseIO`. -/
abbrev Env (α : Type) : Type := EnvT BaseIO α

namespace Env

/-! ### Monad-related instances -/
section monad_instances variable [Monad m]

/-- Provides an instance by unfolding `EnvT` and running inference. -/
private def infer {α : Sort u} (a : α := by unfold EnvT ; infer_instance) : α := a

instance : Monad (EnvT m) := infer
example : Monad Env := inferInstance

instance : MonadExceptOf Error (EnvT m) := infer
example : MonadExceptOf Error Env := inferInstance

instance : MonadLift m (EnvT m) := infer
example : MonadLift BaseIO Env := inferInstance

instance : MonadLift (Except Error) (EnvT m) := infer

instance [L : MonadLiftT BaseIO m] : MonadLift Env (EnvT m) where
  monadLift code := return ← L.monadLift code
example : MonadLift Env (EnvT IO) := inferInstance

instance [MonadLiftT BaseIO m] : MonadLift IO (EnvT m) where
  monadLift code := do
    match ← code.toBaseIO with
    | .ok a => return a
    | .error e => Error.mk e.toString |> throw
example [MonadLiftT BaseIO m] : MonadLiftT BaseIO (EnvT m) := inferInstance
example : MonadLift IO Env := inferInstance
end monad_instances

/-! ### Exports for the C++ layer -/
section cpp_exports

@[export env_pure]
private def env_pure (a : α) : Env α := return a

@[export env_bool]
private def env_bool (b : Bool) : Env Bool := return b

@[export env_uint64]
private def env_uint64 (u : UInt64) : Env UInt64 := return u

@[export env_throw]
private def env_throw (e : Error) : Env α := throw e

@[export env_throw_string]
private def env_throw_string (msg : String) : Env α := Error.mk msg |> throw

end cpp_exports

/-! ### Runners -/
section runners variable [Monad m]

/-- Runs `EnvT` code. -/
def run [MonadLiftT BaseIO m] : EnvT m α → m (Except Error α) := id

/-- Runs `EnvT` code in `IO`. -/
def runIO [MonadLiftT m IO] (code : EnvT m α) : IO α := do
  match ← code.run with
  | .ok a => return a
  | .error e => IO.userError e.toString |> throw

end runners

end Env

@[inherit_doc Env.run]
protected abbrev EnvT.run := @Env.run

@[inherit_doc Env.run]
protected abbrev run := @Env.run



/-! ## Basic export for the C++ layer -/



namespace CppExports

@[export prod_mk]
private def mkProd := @Prod.mk

end CppExports



/-! ## DSL for definition  DRY -/
section defsMacro



open Lean
open Elab
open Command (CommandElab CommandElabM)

declare_syntax_cat externKw

declare_syntax_cat defsItem
declare_syntax_cat defsItemHead
declare_syntax_cat defsItemTail!?
declare_syntax_cat defsItemTail

declare_syntax_cat defsMod

/-- Arity of an expression.

Stolen from [batteries].

[batteries]: https://leanprover-community.github.io/mathlib4_docs/Batteries/Lean/Expr.html#Lean.Expr.forallArity
-/
def forallArity : Expr → Nat
  | .mdata _ b => forallArity b
  | .forallE _ _ body _ => 1 + forallArity body
  | _ => 0

syntax "?" : defsMod
syntax "!" : defsMod
syntax "!?" : defsMod
syntax "?!" : defsMod

scoped syntax (name := defsItemStxHead)
  declModifiers
  ("@[" "force" str "]")?
  "def " defsMod ? ident
: defsItemHead

scoped syntax (name := defsItemStxTail!?)
  withPosition(ppLine "with!? "
    group(
      colGt
      docComment ?
      ident
    )*
  )
: defsItemTail!?

scoped syntax (name := defsItemStxTail)
  withPosition(ppLine "with "
    group(
      colGt
      docComment ?
      declId optDeclSig ":= " withPosition(group(colGe term))
    )*
  )
: defsItemTail

scoped syntax (name := defsItemStx)
  defsItemHead
  declSig
  (defsItemTail!?)?
  (defsItemTail)?
: defsItem

unsafe def elabDefsItem
  (pref : String) (forceMods : Option (TSyntax `defsMod))
: CommandElab
| `(defsItem|
    $mods:declModifiers
    $[ @[ force $forcedName ] ]?
    def $ident:ident $identSig:declSig
    $[ with!? $[
        $[$autoDoc]?
        $autoId
    ]* ]?
    $[ with $[
        $[$subDoc]?
        $subId $subSig := $subDef
    ]* ]?
) => do
  if let some defMods := forceMods then
    let stx ← `(defsItem|
$mods:declModifiers
$[ @[ force $forcedName ] ]?
def $defMods $ident:ident $identSig:declSig
$[ with!? $[
    $[$autoDoc]?
    $autoId
]* ]?
$[ with $[
    $[$subDoc]?
    $subId $subSig := $subDef
]* ]?
    )
    return ← elabDefsItem pref none stx

  let externName :=
    let id :=
      if let some forcedName := forcedName then
        forcedName.getString
      else
        ident.getId.toString
    pref ++ "_" ++ id |> Syntax.mkStrLit
  -- println! "extern name := `{externName}`"
  let mods ←
    match mods with
    | `(Parser.Command.declModifiersT|
      $[$doc:docComment]? $[@[ $[ $attrs ],* ]]? $[$vis]? $[$isNc]? $[$isUnsafe]? $[$opt]?
    ) => do
      let ext ← `(Parser.Term.attrInstance| extern $externName:str)
      let attrs := attrs.getD #[] |>.push ext
      `(Parser.Command.declModifiersT|
        $[$doc:docComment]? @[ $[$attrs],* ] $[$vis]? $[$isNc]? $[$isUnsafe]? $[$opt]?
      )
    | _ => throwUnsupportedSyntax
  let mainDef ←`(
    set_option linter.unusedVariables false in
    $(⟨mods⟩):declModifiers
    opaque $ident:declId $identSig
  )
  Command.elabCommand mainDef

  let fullName :=
    Lean.Name.mkSimple ident.getId.toString
    |> (← Elab.liftMacroM Macro.getCurrNamespace).append
  let fullIdent := Lean.mkIdent fullName

  let define doc? id sig? (body : Syntax.Term) : CommandElabM _ := do
    if let some doc := doc? then
      `(command|
        $doc:docComment
        def $id:declId $sig?:optDeclSig := $body
      )
    else
      `(command|
        @[inherit_doc $fullIdent]
        def $id:declId $sig?:optDeclSig := $body
      )

  if let (some autoDoc?, some autoId) := (autoDoc, autoId) then
    let env ← getEnv
    let arity ←
      if let some (.opaqueInfo i) := env.find? fullName then
        pure (forallArity i.type)
      else
        throwError s!"failed to retrieve arity of (opaque) function `{ident}`"

    let mut args := Array.empty
    for i in [0:arity] do
      let arg := Lean.Name.mkSimple s!"v{i}" |> Lean.mkIdent
      args := args.push arg
    let funCall : TSyntax `term ← `(term| ( $fullIdent $[ $args ]* ))

    for (autoDoc?, autoId) in autoDoc?.zip autoId do
      let id : String := autoId.getId.toString
      let body ←
        if id.endsWith "!" then
          let unwrapName := Lean.Name.mkStr3 "cvc5" "Error" "unwrap!" |> Lean.mkIdent
          `(fun $[$args]* => $funCall |> $unwrapName)
        else if id.endsWith "?" then
          `(fun $[$args]* => $funCall |> Except.toOption)
        else
          throwError s!"unexpected auto function name `{id}`: expected `<ident>!` or `<ident>?`"
      let cmd ← define autoDoc? autoId (← `(optDeclSig|)) body
      Command.elabCommand cmd

  if let
    (some subDoc?, some subId, some subSig, some subDef)
    := (subDoc, subId, subSig, subDef)
  then
    let all := subDoc?.zip subId |>.zip subSig |>.zip subDef
    for (((subDoc?, subId), subSig), subDef) in all do
      Command.elabCommand
        (← define subDoc? subId subSig subDef)
| `(defsItem|
    $mods:declModifiers
    $[ @[ force $forcedName ] ]?
    def $defsMod $ident:ident $identSig:declSig
    $[ with $[
        $[$subDoc]?
        $subId $subSig := $subDef
    ]* ]?
) => do
  let name := ident.getId
  let identOpt _ := name.appendAfter "?" |> Lean.mkIdent
  let identPanic _ := name.appendAfter "!" |> Lean.mkIdent
  let auto : Array Ident ←
    match defsMod with
    | `(defsMod| ?) => pure #[identOpt ()]
    | `(defsMod| !) => pure #[identPanic ()]
    | `(defsMod| ?!)
    | `(defsMod| !?) => pure #[identOpt (), identPanic ()]
    | _ => throwUnsupportedSyntax
  let stx ← `(defsItemStx|
    $mods:declModifiers
    $[ @[ force $forcedName ] ]?
    def $ident:ident $identSig:declSig
    with!? $[ $auto:ident ]*
    $[ with $[
        $[ $subDoc:docComment ]?
        $subId:declId $subSig:optDeclSig := $subDef:term
    ]* ]?
  )
  elabDefsItem pref none stx
| _ => throwUnsupportedSyntax

/-- Defines similar functions realized by `extern`.

```
extern! in "prefix"
  /-- Create a Boolean constant.

  - `b`: The Boolean constant.

  Will create an opaque definition with `[@extern extStr]` where
  `extStr = "prefix" ++ "_" ++ "myFunction"`.
  -/
  def myFunction : Term → Except Error Op
  with!?
    endsWithBang!
    endWithQuestion?
  with
    myOtherFunction : Term → Op :=
      Error.unwrap! ∘ myFunction
    /-- Optional function docstring: if none, inherit from the main function. -/
    yetAnotherFunction : Term → Option Op :=
      Except.toOption ∘ myFunction
```

- `in "prefix"` is optional; if none, then the prefix will be the (last component of the) name of
  the current namespace with the first letter lowercased. Fails if the current namespace has no
  components.

- `with ...`: takes a sequence of identifiers, each generate a function that
  - unwraps the result if `!`-ended, which generates code similar to `myOtherFunction` above;
  - turns a result into an option if `?`-ended, which generates code similar to `yetAnotherFunction`
    above;
  - fails otherwise.

  The `with ...` syntax is currently only compatible with external functions that produce `Except
  Error α` values.

- Supports `declModifiers` on the main (`def`) function `myFunction` such as `private`.
- Accepts a list of external (`def`) functions, each with its `with` clauses.

This macro can generate optional (`?`) and panic (`!`) wrappers even more automatically.

```
extern! "prefix"
  /-- Create a Boolean constant.

  - `b`: The Boolean constant.

  Will create an opaque definition with `[@extern extStr]` where
  `extStr = "prefix" ++ "_" ++ "myFunction"`.
  -/
  def !? myFunction : Term → Except Error Op
  with
    myOtherFunction : Term → Op :=
      myFunction!
    /-- Optional function docstring: if none, inherit from the main function. -/
    yetAnotherFunction : Term → Option Op :=
      myFunction?
```

Notice the `!?` between `def` and `myFunction`. This generates `myFunction!` and `myFunction?` which
respectively panic-unwrap errors and turn the `Except` into an `Option`. In other words, it is the
same as (and internally turned into) a `with!? myFunction! myFunction?` clause using the first
syntax above.

Besides `!?`, the following are also supported:
- `?!`: same behavior as `!?`;
- `!`: only generate the panic unwrapper;
- `?`: only generate the `Option` unwrapper.
-/
scoped syntax (name := multidefs)
  withPosition("external! " ("in " str)? ppLine group(colGt defsItem)+)
: command

@[inherit_doc multidefs, command_elab multidefs]
unsafe def multidefsImpl : CommandElab
| `(command|
  external! $[in $pref:str]? $[$defsItems]*
) => do
  let ns ← getCurrNamespace
  let pref ←
    if let some pref := pref then
      pure pref.getString
    else
      -- println! "componentsRev for {ns.toString}"
      -- for c in ns.componentsRev do
      --   println! "- {c.toString}"
      if let super::_ := ns.componentsRev then
        let mut super := super.toString
        if 0 < super.length then
          super := String.Pos.Raw.get super 0 |>.toLower |> String.Pos.Raw.set super 0
        -- println! "-> `{super}`"
        pure super
      else
        throwError "failed to retrieve current workspace, please provide an explicit prefix"
  for defsItem in defsItems do
    elabDefsItem pref none defsItem
| _ => throwUnsupportedSyntax

scoped syntax (name := externkw)
  ("extern_def " <|> "extern_def! " <|> "extern_def? " <|> "extern_def!? " <|> "extern_def?! ")
: externKw

/-- Defines an external, opaque function with optional helpers.

```
/-- Some documentation. -/
extern_def!? in "prefix" myFunction : Term → Except Error Op
```

Generates an opaque definition

```
/-- Some documentation. -/
@[extern "prefix_myFunction"]
def myFunction : Term → Except Error Op
```

- `in "prefix"` is optional, uses the current namespace with first letter lowercased if none.

- `extern_def!?` also defines `myFunction! : Term → Op` and `myFunction? : Term → Option Op` in
  terms of `myFunction`.

  Other variants exist:
  - `extern_def?!`: same as `extern_def!?`;
  - `extern_def?`: only defines `myFunction?`;
  - `extern_def!`: only defines `myFunction!`;
  - `extern_def`: defines nothing besides `myFunction`.
-/
scoped syntax (name := externdef)
  declModifiers
  withPosition(
    externKw
    ("in " str)?
    ident declSig (defsItemTail)?
  )
: command

@[inherit_doc externdef, command_elab externdef]
unsafe def externdefImpl : CommandElab
| `(command|
  $mods:declModifiers
  $externKw $[in $path:str]? $ident $sig $[$tail]?
) => do
  let defMod ←
    match externKw with
    | `(externKw| extern_def) => pure none
    | `(externKw| extern_def!) => `(defsMod| !)
    | `(externKw| extern_def?) => `(defsMod| ?)
    | `(externKw| extern_def!?) => `(defsMod| !?)
    | `(externKw| extern_def?!) => `(defsMod| ?!)
    | _ => throwUnsupportedSyntax
  let stx ← `(
    external! $[in $path]?
      $mods:declModifiers
      def $[$defMod]? $ident $sig $[$tail:defsItemTail]?
  )
  Command.elabCommand stx
| _ => throwUnsupportedSyntax

end defsMacro



/-! ## Definitions over auto-generated types -/



namespace Kind

/-- Produces a string representation. -/
protected extern_def toString : Kind → String
instance : ToString Kind := ⟨Kind.toString⟩

/-- Produces a hash. -/
extern_def hash : Kind → UInt64
instance : Hashable Kind := ⟨Kind.hash⟩

end Kind



namespace SortKind

/-- Produces a string representation. -/
protected extern_def toString : SortKind → String
instance : ToString SortKind := ⟨SortKind.toString⟩

/-- Produces a hash. -/
extern_def hash : SortKind → UInt64
instance : Hashable SortKind := ⟨SortKind.hash⟩

end SortKind



namespace ProofRule

/-- Produces a string representation. -/
protected extern_def toString : ProofRule → String
instance : ToString ProofRule := ⟨ProofRule.toString⟩

/-- Produces a hash. -/
extern_def hash : ProofRule → UInt64
instance : Hashable ProofRule := ⟨ProofRule.hash⟩

end ProofRule



namespace SkolemId

/-- Produces a string representation. -/
protected extern_def toString : SkolemId → String
instance : ToString SkolemId := ⟨SkolemId.toString⟩

/-- Produces a hash. -/
extern_def hash : SkolemId → UInt64
instance : Hashable SkolemId := ⟨SkolemId.hash⟩

end SkolemId



namespace ProofRewriteRule

/-- Produces a string representation. -/
protected extern_def toString : ProofRewriteRule → String
instance : ToString ProofRewriteRule := ⟨ProofRewriteRule.toString⟩

/-- Produces a hash. -/
extern_def hash : ProofRewriteRule → UInt64
instance : Hashable ProofRewriteRule := ⟨ProofRewriteRule.hash⟩

end ProofRewriteRule



namespace UnknownExplanation

/-- Produces a string representation. -/
protected extern_def toString : UnknownExplanation → String
instance : ToString UnknownExplanation := ⟨UnknownExplanation.toString⟩

/-- Produces a hash. -/
extern_def hash : UnknownExplanation → UInt64
instance : Hashable UnknownExplanation := ⟨UnknownExplanation.hash⟩

end UnknownExplanation

namespace RoundingMode

/-- Produces a string representation. -/
protected extern_def toString : RoundingMode → String
instance : ToString RoundingMode := ⟨RoundingMode.toString⟩

/-- Produces a hash. -/
extern_def hash : RoundingMode → UInt64
instance : Hashable RoundingMode := ⟨RoundingMode.hash⟩

end RoundingMode



namespace BlockModelsMode

/-- Produces a string representation. -/
protected extern_def toString : BlockModelsMode → String
instance : ToString BlockModelsMode := ⟨BlockModelsMode.toString⟩

/-- Produces a hash. -/
extern_def hash : BlockModelsMode → UInt64
instance : Hashable BlockModelsMode := ⟨BlockModelsMode.hash⟩

end BlockModelsMode



namespace LearnedLitType

/-- Produces a string representation. -/
protected extern_def toString : LearnedLitType → String
instance : ToString LearnedLitType := ⟨LearnedLitType.toString⟩

/-- Produces a hash. -/
extern_def hash : LearnedLitType → UInt64
instance : Hashable LearnedLitType := ⟨LearnedLitType.hash⟩

end LearnedLitType



namespace ProofComponent

/-- Produces a string representation. -/
protected extern_def toString : ProofComponent → String
instance : ToString ProofComponent := ⟨ProofComponent.toString⟩

/-- Produces a hash. -/
extern_def hash : ProofComponent → UInt64
instance : Hashable ProofComponent := ⟨ProofComponent.hash⟩

end ProofComponent



namespace ProofFormat

/-- Produces a string representation. -/
protected extern_def toString : ProofFormat → String
instance : ToString ProofFormat := ⟨ProofFormat.toString⟩

/-- Produces a hash. -/
extern_def hash : ProofFormat → UInt64
instance : Hashable ProofFormat := ⟨ProofFormat.hash⟩

end ProofFormat



namespace FindSynthTarget

/-- Produces a string representation. -/
protected extern_def toString : FindSynthTarget → String
instance : ToString FindSynthTarget := ⟨FindSynthTarget.toString⟩

/-- Produces a hash. -/
extern_def hash : FindSynthTarget → UInt64
instance : Hashable FindSynthTarget := ⟨FindSynthTarget.hash⟩

end FindSynthTarget



namespace InputLanguage

/-- Produces a string representation. -/
protected extern_def toString : InputLanguage → String
instance : ToString InputLanguage := ⟨InputLanguage.toString⟩

/-- Produces a hash. -/
extern_def hash : InputLanguage → UInt64
instance : Hashable InputLanguage := ⟨InputLanguage.hash⟩

end InputLanguage



/-! ## Basic cvc5 types -/



private opaque ResultImpl : NonemptyType.{0}

/-- Encapsulation of a three-valued solver result, with explanations. -/
def Result : Type := ResultImpl.type

namespace Result

instance : Nonempty Result := ResultImpl.property

end Result



private opaque SynthResultImpl : NonemptyType.{0}

/-- Encapsulation of a three-valued solver result, with explanations. -/
def SynthResult : Type := SynthResultImpl.type

namespace SynthResult

instance : Nonempty SynthResult := SynthResultImpl.property

end SynthResult



private opaque DatatypeConstructorDeclImpl : NonemptyType.{0}

/-- A cvc5 datatype constructor declaration.

A datatype constructor declaration is a specification used for creating a datatype constructor.
-/
def DatatypeConstructorDecl : Type := DatatypeConstructorDeclImpl.type

namespace DatatypeConstructorDecl

instance : Nonempty DatatypeConstructorDecl := DatatypeConstructorDeclImpl.property

/-- A string representation of this datatype constructor declaration. -/
protected extern_def toString : DatatypeConstructorDecl → String

instance : ToString DatatypeConstructorDecl := ⟨DatatypeConstructorDecl.toString⟩

end DatatypeConstructorDecl



private opaque DatatypeDeclImpl : NonemptyType.{0}

/-- A cvc5 datatype declaration.

A datatype declaration is not itself a datatype (see `Datatype`), but a specification for creating a
datatype sort.

The interface for a datatype declaration coincides with the syntax for the SMT-LIB 2.6 command
`declare-datatype`, or a single datatype within the `declare-datatypes` command.

`Datatype` sorts can be constructed from a `DatatypeDecl` using:
- `Solver.mkDatatypeSort`
- `Solver.mkDatatypeSorts`
-/
def DatatypeDecl : Type := DatatypeDeclImpl.type

namespace DatatypeDecl

instance : Nonempty DatatypeDecl := DatatypeDeclImpl.property

/-- Get a string representation of this datatype declaration. -/
protected extern_def toString : DatatypeDecl → String

instance : ToString DatatypeDecl := ⟨DatatypeDecl.toString⟩

end DatatypeDecl



private opaque DatatypeSelectorImpl : NonemptyType.{0}

/-- A cvc5 datatype selector. -/
def DatatypeSelector : Type := DatatypeSelectorImpl.type

namespace DatatypeSelector

instance : Nonempty DatatypeSelector := DatatypeSelectorImpl.property

/-- Gte the string representation of this datatype selector. -/
protected extern_def toString : DatatypeSelector → String

instance : ToString DatatypeSelector := ⟨DatatypeSelector.toString⟩

end DatatypeSelector



private opaque DatatypeConstructorImpl : NonemptyType.{0}

/-- A cvc5 datatype constructor. -/
def DatatypeConstructor : Type := DatatypeConstructorImpl.type

namespace DatatypeConstructor

instance : Nonempty DatatypeConstructor := DatatypeConstructorImpl.property

/-- A string representation of this datatype. -/
protected extern_def toString : DatatypeConstructor → String

instance : ToString DatatypeConstructor := ⟨DatatypeConstructor.toString⟩

end DatatypeConstructor



private opaque DatatypeImpl : NonemptyType.{0}

/-- A cvc5 datatype. -/
def Datatype : Type := DatatypeImpl.type

namespace Datatype

instance : Nonempty Datatype := DatatypeImpl.property

/-- A string representation of this datatype. -/
protected extern_def toString : Datatype → String

instance : ToString Datatype := ⟨Datatype.toString⟩

end Datatype



private opaque GrammarImpl : NonemptyType.{0}

/-- A Sygus Grammar.

This class can be used to define a context-free grammar of terms. Its interface coincides with the
definition of grammars in the SyGuS IF 2.1 standard.
-/
def Grammar : Type := GrammarImpl.type

namespace Grammar

instance : Nonempty Grammar := GrammarImpl.property

/-- A string representation of this grammar. -/
protected extern_def toString : Grammar → String

instance : ToString Grammar := ⟨Grammar.toString⟩

end Grammar



private opaque CommandImpl : NonemptyType.{0}

/-- Encapsulation of a command.

Commands are constructed by the `InputParser` and can be invoked on the `Solver` and
`Command`.
-/
def Command : Type := CommandImpl.type

namespace Command

instance : Nonempty Command := CommandImpl.property

/-- Get a string representation of this command. -/
protected extern_def toString : Command → String

instance : ToString Command := ⟨Command.toString⟩

end Command
