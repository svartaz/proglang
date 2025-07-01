import Std.Data.HashMap
import Init.Data.List.Basic

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
def FormIdent := String

@[reducible]
def TermIdent := String

inductive Form
| var: FormIdent → Form
| con: FormIdent → Form
| to: Form → Form → Form
deriving BEq

def Form.toString
: Form → String
| var a => a
| con a => a
| to φ χ => s!"({φ.toString} > {χ.toString})"

instance: ToString Form where
  toString := Form.toString

partial def Form.free (φ: Form): List FormIdent :=
  let rec go (as: List FormIdent) (φ: Form): List FormIdent :=
    match φ with
    | Form.var a => if as.contains a then as else a :: as
    | Form.con _ => as
    | Form.to φ χ => go (go as φ) χ
  go [] φ |>.reverse

def Form.rename (map: Std.HashMap FormIdent FormIdent)
: Form → Form
| Form.var a => Form.var (map.getD a a)
| Form.con x => Form.con x
| Form.to φ χ => (rename map φ).to (rename map χ)

inductive Pattern
| var: TermIdent → Pattern
| con: TermIdent → Pattern
| conApp: TermIdent → Pattern → Pattern

def Pattern.toString: Pattern → String
| Pattern.var x => x
| Pattern.con x => x
| Pattern.conApp x p => s!"{x} {p.toString}"

instance: ToString Pattern where
  toString := Pattern.toString

def Pattern.occur: Pattern → TermIdent → Bool
| Pattern.var x, y => x == y
| Pattern.con _, _ => false
| Pattern.conApp _ p, x => p.occur x

inductive Term
| ann: Term → Form → Term
| var: TermIdent → Term
| con: TermIdent → Term
| abs: TermIdent → Option Form → Term → Term
| app: Term → Term → Term
| fix: TermIdent → TermIdent → Option Form → Term → Term
| mat: Term → List (Pattern × Term) → Term

partial def Term.toString
: Term → String
| Term.ann t φ => s!"({t.toString}: {φ.toString})"
| Term.var a => a
| Term.con x => x
| Term.abs x none t => s!"({x} ↦ {t.toString})"
| Term.abs x (some φ) t => s!"({x}: {φ} ↦ {t.toString})"
| Term.app t u => s!"({t.toString} {u.toString})"
| Term.fix r x none t => s!"(fix {r} {x} ↦ {t.toString})"
| Term.fix r x (some φ) t => s!"(fix {r} {x}: {φ} ↦ {t.toString})"
| Term.mat t alts =>
  s!"({t.toString} " ++
  " ".intercalate (alts.map fun (p, u) => s!"| {p.toString}, {u.toString}") ++
  ")"

instance: ToString Term where
  toString := Term.toString

partial def Term.free: Term → TermIdent → Bool
| ann t _, x => t.free x
| var x, y => x == y
| con _, _ => false
| abs x _ t, y => x != y && t.free y
| app t u, x => t.free x || u.free x
| fix f x _ t, y => x != y && f != y && t.free y
| mat t alts, x => t.free x || alts.any fun (p, u) =>
  (p.occur x).not && u.free x

def Term.absPlu: List (TermIdent × Option Form) → Term → Term
| [], t => t
| (x, φ) :: xs, t => Term.abs x φ $ Term.absPlu xs t

def Term.appPlu: Term → List Term → Term
| t, [] => t
| t, u :: us => (t.app u).appPlu us

structure Env where
  cons: Std.HashMap TermIdent Form
  vars: Std.HashMap TermIdent Form
  subs: Std.HashMap FormIdent Form
deriving BEq

def Form.occur
: Form → FormIdent → Bool
| var a, b => a == b
| con _, _ => false
| to φ χ, a => φ.occur a || χ.occur a

partial def Env.fresh (env: Env): String :=
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
| Form.con x => Form.con x
| Form.to φ χ => (env.substituteOnce φ).to (env.substituteOnce χ)

partial def Env.substitute (env: Env) (φ: Form): Form :=
  let φ' := env.substituteOnce φ
  if φ == φ' then φ else env.substitute φ'

partial def Env.unify (env: Env)
: Form → Form → String ⊕ Env
| Form.con a, Form.con a' =>
  if a = a'
    then pure env
    else Sum.inl s!"unify: con: {a} is not {a'}"
| Form.var a, Form.var a' =>
  if a = a'
    then pure env
    else pure {env with subs := env.subs.insert a' (Form.var a)}
| Form.var a, φ =>
  if φ.occur a
    then Sum.inl s!"unify: {a} occureth in {φ}"
    else
      match env.subs.get? a with
      | none => pure { env with subs := env.subs.insert a φ }
      | some φ' => unify env φ φ'
| φ, Form.var a => env.unify (Form.var a) φ
| Form.to φ0 φ1, Form.to χ0 χ1 => do
  let env' ← unify env φ0 χ0
  env'.unify φ1 χ1
| φ, χ => Sum.inl s!"unify: default: {φ} is not {χ}"

def Env.checkPattern (env: Env)
: Pattern → Form → String ⊕ Env
| Pattern.var x, φ => pure { env with vars := env.vars.insert x φ}
| Pattern.con x, φ =>
  match env.cons.get? x with
  | none => Sum.inl s!"checkPattern: con: i know not {x}"
  | some φ' => env.unify φ φ'
| Pattern.conApp a p, φ =>
  match env.cons.get? a with
  | none => Sum.inl s!"checkPattern: conApp: i know not {a}"
  | some (Form.to χ φ') => do
    let env' ← env.unify φ φ'
    env'.checkPattern p χ
  | some _ => Sum.inl s!"checkPattern: conApp: NEVER HAPPEN"

mutual
  partial def Env.check
    (env: Env)
    (t: Term)
    (φ: Form)
  : String ⊕ Env := do
    let (φ_t, env_t) ← infer env t
    env_t.unify φ φ_t

  partial def Env.infer (env: Env)
  : Term → String ⊕ Form × Env
  | Term.ann t φ => Prod.mk φ <$> env.check t φ
  | Term.var x => match env.vars.get? x with
    | some φ => pure (φ, env)
    | none => Sum.inl s!"infer: var: i know not {x}"
  | Term.con x => match env.cons.get? x with
    | some φ => pure (φ, env)
    | none => Sum.inl s!"infer: con: i know not {x}"
  | Term.abs x φ t => do
    let φ := φ.getD (Form.var (env.fresh))
    let (φ_t, env_t) ← {env with vars := env.vars.insert x φ}.infer t
    pure (env_t.substitute φ |>.to φ_t, env_t)
  | Term.app t u => do
    let (φ_t, env_t) ← env.infer t
    match φ_t with
    | Form.to φ0 φ1 => Prod.mk φ1 <$> env_t.check u φ0
    | _ => Sum.inl s!"infer: app: {φ_t} is not type of function"
  | Term.fix f x φ t => do
    let (φ, χ) :=
      match φ with
      | none =>
        let a := env.fresh
        let b := {env with subs := env.subs.insert a (Form.var "temp")}.fresh
        (Form.var a, Form.var b)
      | some φ => (φ, Form.var (env.fresh))
    let φ_f := φ.to χ
    let env_f := {env with vars := env.vars.insert x φ |>.insert f φ_f}
    let (φ_t, env_t) ← env_f.infer t
    let env_unify ← env_t.unify χ φ_t
    pure (env_unify.substitute φ_f, env_unify)
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
| Pattern.con x, Term.con x' => if x == x'
  then pure terms
  else Sum.inl s!"destruct: con: {x} is not {x'}"
| Pattern.conApp x p, Term.app (Term.con x') t => if x == x'
  then Term.destruct terms p t
  else Sum.inl s!"destruct: app: {x} is not {x'}"
| p, t => Sum.inl s!"destruct: default: {p} is not {t}"

partial def Term.reduce (terms: Terms): Term → Term
| ann t _ => reduce terms t
| var x => terms.getD x (var x)
| con x => con x
| abs x φ t => abs x φ (reduce (terms.erase x) t)
| fix r x φ t => fix r x φ (reduce (terms.erase x) t)
| app t u =>
  let t' := reduce terms t
  let u' := reduce terms u
  match t' with
  | abs x _ t'' => reduce (terms.insert x u') t''
  | fix r x _ t'' =>
    let terms' := terms.insert x u' |>.insert r t'
    reduce terms' t''
  | _ => app t' u'
| mat t alts =>
  let t' := reduce terms t
  let alts' := alts.flatMap fun (p, u) =>
    match Term.destruct terms p t' with
    | Sum.inl _ => []
    | Sum.inr terms => [(u, terms)]
  match alts' with
  | [] => mat t' alts
  | (u, terms') :: _ => reduce terms' u

inductive Decl
| name: TermIdent → List (TermIdent × Option Form) → (Option Form) → Term → Decl
| fix: TermIdent → TermIdent → Term → Decl
| data: String → List (String × List Form) → Decl

def toPlu: List Form → Form → Form
| [], χ => χ
| φ :: φs, χ => Form.to φ (toPlu φs χ)

def Form.minimise (φ: Form): Form :=
  let frees := φ.free
  let (map, _) := frees.foldl (fun (map, n) a =>
      (map.insert a s!"a{n}", n + 1)
    ) (Std.HashMap.emptyWithCapacity, 0)
  φ.rename map

def Form.result: Form → Form
| to _ χ => χ.result
| it => it

partial def Env.interpret
  (env: Env)
  (terms: Terms)
: List Decl → String ⊕ Term × Form × List (String × Form)
| [] => match terms.get? "main" with
  | none => Sum.inl "i know not `main`"
  | some t => do
    let (φ, _) ← env.infer t
    pure (
      Term.reduce terms t,
      env.substitute φ,
      terms.toList.map fun (x, _) =>
        (x, env.vars.getD x (Form.var "unknown"))
    )
| Decl.name f xs χ t :: decls => do
  let idents := f :: xs.map fun (x, _) => x
  if idents.any fun ident => (idents.erase ident).contains ident
    then Sum.inl s!"interpret: name: duplicate identifiers {idents}"
    else

    if t.free f
      then match xs with
      | [] => Sum.inl s!"interpret: name: recursive without parameter {f}"
      | (x, _) :: xs' =>
        let t' := match χ with
        | none => Term.fix f x none (Term.absPlu xs' t)
        | some χ => Term.fix f x none (Term.absPlu xs' (Term.ann t χ))
        let (φ, env') ← env.infer t'
        {env' with vars := env'.vars.insert f φ}.interpret
          (terms.insert f t')
          decls
      else
        let t' := Term.absPlu xs $
          match χ with
          | none => t
          | some χ => Term.ann t χ
        let (φ, env') ← env.infer t'
        {env' with vars := env'.vars.insert f φ}.interpret
          (terms.insert f t')
          decls
| Decl.fix r x t :: decls =>
  env.interpret terms $ Decl.name r [] none (Term.fix r x none t) :: decls
| Decl.data a cs :: decls =>
  {env with
    cons :=
      cs.foldl (fun cons (c, φs) => cons.insert c (toPlu φs (Form.con a))) env.cons
  }.interpret
    terms
    decls

#eval ({
  cons := Std.HashMap.emptyWithCapacity,
  vars := Std.HashMap.emptyWithCapacity,
  subs := Std.HashMap.emptyWithCapacity,
}: Env).interpret
  Std.HashMap.emptyWithCapacity
  [
    Decl.data "'one" [
      ("()", [])],
    Decl.data "'two" [
      ("true", []),
      ("false", [])],
    Decl.data "'nat" [
      ("zero", []),
      ("succ", [Form.var "nat"])],
    Decl.name "id" [("x", none)] none $ Term.var "x",
    Decl.name "const" [("x", none), ("y", none)] none $ (Term.var "x"),
    Decl.name "not" [("x", none)] none $
      Term.mat (Term.var "x") [
        (Pattern.con "true", Term.con "false"),
        (Pattern.con "false", Term.con "true"),
      ],
    Decl.name "if" [
      ("x", none),
      ("then", none),
      ("else", none),
    ] none $
      Term.mat (Term.var "x") [
        (Pattern.con "true", Term.var "then"),
        (Pattern.con "false", Term.var "else"),
      ],
    Decl.name "even" [("x", none)] none $
      Term.mat (Term.var "x") [
        (Pattern.con "zero",
          Term.con "true"),
        (Pattern.conApp "succ" (Pattern.var "x_"),
          (Term.var "not").app ((Term.var "even").app (Term.var "x_")))
      ],
    Decl.name "zero_is_even" [] none $
      Term.app (Term.var "even") (Term.con "zero"),
    Decl.name "one_is_even" [] none $
      Term.app (Term.var "even") (Term.app (Term.con "succ") (Term.con "zero")),
    Decl.name "main" [] none $
      Term.appPlu (Term.var "if") [
        Term.con "false",
        Term.con "zero",
        Term.app (Term.con "succ") (Term.con "zero")
      ]
  ]
