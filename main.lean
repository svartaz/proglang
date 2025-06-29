import Std.Data.HashMap

namespace Std.HashMap
  instance [BEq α] [Hashable α] [BEq β]: BEq (Std.HashMap α β) where
    beq a b :=
      a.keys.all (b.contains ·) &&
      b.keys.all (fun k => a.contains k && a.get? k == b.get? k)
end Std.HashMap

instance : Monad (Sum α) where
  pure := Sum.inr
  bind := fun
  | Sum.inl a, _ => Sum.inl a
  | Sum.inr a, f => f a

@[reducible]
def formIdent := String

@[reducible]
def termIdent := String

@[reducible]
def conIdent := String

inductive Form
| var: formIdent → Form
| con: formIdent → Form
| to: Form → Form → Form
deriving BEq

def Form.toString
: Form → String
| var a => a
| con c => c
| to φ χ => s!"({φ.toString} > {χ.toString})"

instance: ToString Form where
  toString := Form.toString

partial def Form.free (φ: Form): List formIdent :=
  let rec go (as: List formIdent) (φ: Form): List formIdent :=
    match φ with
    | Form.var a => if as.contains a then as else a :: as
    | Form.con _ => as
    | Form.to φ χ => go (go as φ) χ
  go [] φ |>.reverse

def Form.rename (map: Std.HashMap formIdent formIdent)
: Form → Form
| Form.var a => Form.var (map.getD a a)
| Form.con c => Form.con c
| Form.to φ χ => (rename map φ).to (rename map χ)

inductive Pattern
| var: termIdent → Pattern
| con: conIdent → Pattern
| app: conIdent → Pattern → Pattern

def Pattern.toString: Pattern → String
| Pattern.var x => x
| Pattern.con c => c
| Pattern.app c p => s!"{c} {p.toString}"

instance: ToString Pattern where
  toString := Pattern.toString

inductive Term
| ann: Term → Form → Term
| var: termIdent → Term
| con: conIdent → Term
| abs: termIdent → Option Form → Term → Term
| app: Term → Term → Term
| mat: Term → List (Pattern × Term) → Term

partial def Term.toString
: Term → String
| Term.ann t φ => s!"({t.toString}: {φ.toString})"
| Term.var a => a
| Term.con c => c
| Term.abs x none t => s!"({x} ↦ {t.toString})"
| Term.abs x (some φ) t => s!"({x}: {φ.toString} ↦ {t.toString})"
| Term.app t u => s!"({t.toString} {u.toString})"
| Term.mat t alts =>
  s!"({t.toString} " ++
  " ".intercalate (alts.map fun (p, u) => s!"| {p.toString}, {u.toString}") ++
  ")"

instance: ToString Term where
  toString := Term.toString

structure Env where
  cons: Std.HashMap conIdent Form
  vars: Std.HashMap termIdent Form
  subs: Std.HashMap formIdent Form
deriving BEq

def Form.occur (a: formIdent)
: Form → Bool
| var b => a == b
| con _ => false
| to φ χ => occur a φ || occur a χ

def Env.fresh (env: Env): String :=
  let rec go (n: Nat) :=
    let name := s!"a{n}"
    if env.subs.contains name ||
      env.subs.values.any (·.occur name) ||
      env.vars.values.any (·.occur name) ||
      env.cons.values.any (·.occur name)
    then go (n + 1) else name
  go 0

def Env.substituteOnce (env: Env)
: Form → Form
| Form.var a => env.subs.getD a (Form.var a)
| Form.con c => Form.con c
| Form.to φ χ => (env.substituteOnce φ).to (env.substituteOnce χ)

def Env.substitute (env: Env) (φ: Form): Form :=
  let φ' := env.substituteOnce φ
  if φ == φ' then φ else env.substitute φ'

partial def Env.unify (env: Env)
: Form → Form → String ⊕ Env
| Form.con c, Form.con c' => if c == c'
  then pure env
  else Sum.inl s!"unify: con: {c} is not {c'}"
| Form.var a, Form.var b => if a = b
  then pure env
  else pure {env with subs := env.subs.insert b (Form.var a)}
| Form.var a, φ => if Form.occur a φ
  then Sum.inl s!"unify: {a} occureth in {φ}"
  else match env.subs.get? a with
  | some φ' => unify env φ φ'
  | none => pure { env with subs := env.subs.insert a φ }
| φ, Form.var a => env.unify (Form.var a) φ
| Form.to φ0 φ1, Form.to χ0 χ1 => do
  let env' ← unify env φ0 χ0
  env'.unify φ1 χ1
| φ, χ => Sum.inl s!"unify: default: {φ} is not {χ}"

def Env.checkPattern (env: Env)
: Pattern → Form → String ⊕ Env
| Pattern.var x, φ => pure { env with vars := env.vars.insert x φ}
| Pattern.con c, φ =>
  match env.cons.get? c with
  | none => Sum.inl s!"checkPattern: con: i know not {c}"
  | some φ' => env.unify φ φ'
| Pattern.app c p, φ =>
  match env.cons.get? c with
  | none => Sum.inl s!"checkPattern: app: i know not {c}"
  | some (Form.to χ φ') => do
    let env' ← env.unify φ φ'
    env'.checkPattern p χ
  | some _ => Sum.inl s!"checkPattern: app: NEVER HAPPEN"

mutual
  def Env.check
    (env: Env)
    (t: Term)
    (φ: Form)
  : String ⊕ Env := do
    let (φ', env') ← infer env t
    env'.unify φ φ'

  def Env.infer (env: Env)
  : Term → String ⊕ Form × Env
  | Term.ann t φ => Prod.mk φ <$> env.check t φ
  | Term.var x => match env.vars.get? x with
    | some φ => pure (φ, env)
    | none => Sum.inl s!"infer: var: i know not {x}"
  | Term.con c => match env.cons.get? c with
    | some φ => pure (φ, env)
    | none => Sum.inl s!"infer: con: i know not {c}"
  | Term.abs x none t => do
    let φ := env.vars.getD x (Form.var (env.fresh))
    let (χ, env') ← {env with vars := env.vars.insert x φ}.infer t
    pure (env'.substitute φ |>.to χ, env')
  | Term.abs x (some φ) t => do
    let (χ, env') ← {env with vars := env.vars.insert x φ}.infer t
    pure (φ.to χ, env')
  | Term.app t u => do
    let (φ, env') ← env.infer t
    match φ with
    | Form.to φ0 φ1 => Prod.mk φ1 <$> env'.check u φ0
    | _ => Sum.inl s!"infer: app: {φ} is not type of function"
  | Term.mat t alts => do
    let (φ_t, env_t) ← env.infer t
    match alts with
    | [] => Sum.inl "infer: mat: match with no pattern"
    | (p, u) :: alts' =>
      let env_p ← env_t.checkPattern p φ_t
      let (φ', env_head) ← env_p.infer u
      let env' ← alts'.foldlM (fun env_current (p, u) => do
        let enc_check := { env_t with subs := env_current.subs }
        let φ_subst := enc_check.substitute φ_t
        let env_p ← enc_check.checkPattern p φ_subst
        let (φ_u, env_u) ← env_p.infer u
        env_u.unify (env_u.substitute φ_u) (env_u.substitute φ')
      ) env_head
      pure (env'.substitute φ', env')
end

@[reducible]
def Terms := Std.HashMap String Term

def Term.destruct (terms: Terms)
: Pattern → Term → String ⊕ Terms
| Pattern.var x, t => pure (terms.insert x t)
| Pattern.con c, Term.con c' => if c == c'
  then pure terms
  else Sum.inl s!"destruct: con: {c} is not {c'}"
| Pattern.app c p, Term.app (Term.con c') t => if c == c'
  then Term.destruct terms p t
  else Sum.inl s!"destruct: app: {c} is not {c'}"
| p, t => Sum.inl s!"destruct: default: {p} is not {t}"

def Term.reduce (terms: Terms): Term → Term
| ann t _ => reduce terms t
| var x => terms.getD x (var x)
| con c => con c
| abs x φ t => abs x φ (reduce (terms.erase x) t)
| app t u =>
  let t' := reduce terms t
  let u' := reduce terms u
  match t' with
  | abs x _ t'' => reduce (terms.insert x u') t''
  | _ => app t' u'
| mat t alts =>
  let t' := reduce terms t
  let rec go (alts : List (Pattern × Term)) :=
    match alts with
    | [] => mat t' alts
    | (p, u) :: alts' =>
      match Term.destruct terms p t' with
      | Sum.inr terms' => reduce terms' u
      | Sum.inl _ => go alts'
  go alts

inductive Decl
| alias: String → Option Form → Term → Decl
| data: String → List (String × List Form) → Decl

def toPlu: List Form → Form → Form
| [], χ => χ
| φ :: φs, χ => Form.to φ (toPlu φs χ)

def Env.interpret
  (env: Env)
  (terms: Terms)
: List Decl → String ⊕ (Term × Form)
| [] => match terms.get? "main" with
  | none => Sum.inl "i know not `main`"
  | some t => do
    let (φ, env') ← env.infer t
    let φ_subst := env'.substitute φ
    let frees := φ_subst.free
    let (renamin, _) := frees.foldl (fun (map, n) a =>
        (map.insert a s!"a{n}", n + 1)
      ) (Std.HashMap.emptyWithCapacity, 0)
    let φ_min := φ_subst.rename renamin
    pure (Term.reduce terms t, φ_min)
| Decl.alias x none t :: decls => do
  let (φ, env') ← env.infer t
  {env' with vars := env.vars.insert x φ}.interpret (terms.insert x t) decls
| Decl.alias x (some φ) t :: decls => do
  let env' ← env.check t φ
  {env' with vars := env'.vars.insert x φ}.interpret terms decls
| Decl.data a cs :: decls =>
  {env with
    cons :=
      cs.foldl (fun cons (c, φs) => cons.insert c (toPlu φs (Form.con a))) env.cons
  }.interpret
    terms
    decls

def Term.appPlu: Term → List Term → Term
| t, [] => t
| t, u :: us => (t.app u).appPlu us

#eval! ({
  cons := Std.HashMap.emptyWithCapacity,
  vars := Std.HashMap.emptyWithCapacity,
  subs := Std.HashMap.emptyWithCapacity,
}: Env).interpret
  Std.HashMap.emptyWithCapacity
  [
    Decl.data "'one" [("()", [])],
    Decl.data "'two" [("true", []), ("false", [])],
    Decl.data "'nat" [("zero", []), ("succ", [Form.var "nat"])],
    Decl.alias "id" none $ Term.abs "x" none (Term.var "x"),
    Decl.alias "if" none $
      Term.abs "x" none $
      Term.abs "then" none $
      Term.abs "else" none $
      Term.mat (Term.var "x") [
        (Pattern.con "true", Term.var "then"),
        (Pattern.con "false", Term.var "else"),
      ],
    Decl.alias "main" none $
      Term.appPlu (Term.var "if") [
        Term.con "false",
        Term.con "zero",
        Term.app (Term.con "succ") (Term.con "zero")

      ]
  ]
