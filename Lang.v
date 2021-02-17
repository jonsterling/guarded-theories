Require Import Unicode.Utf8 ssreflect.
Require Import GuardedLF.

(* This is a relatively simple theory of typed λ-calculus with
recursive types; every type is made to be an algebra for the later
modality. *)

Axiom tp : ◻.
Axiom tm : tp → Type.

Notation "[ A ]" := (tm A).

Axiom bool : tp.
Axiom arr : tp → tp → tp.
Axiom prod : tp → tp → tp.
Axiom rec : (tp → tp) → tp.

Infix "⇒" := arr (right associativity, at level 60).
Infix "×" := prod (right associativity, at level 60).
Notation "rec: X ; B" := (rec (λ X, B)) (at level 100).

Axiom θ : ∀ {A}, ▷ [A] → [A].
Definition δ {A} (e : [A]) : [A] := θ (next e).

Notation "θ: e" := (θ e) (at level 100).
Notation "δ: e" := (δ e) (at level 100).
Notation "θ[ A ]" := (@θ A).
Notation "δ[ A ]" := (@δ A).

Axiom def_arr : ∀ {A B}, ([A] → [B]) ≅ [A ⇒ B].
Axiom def_prod : ∀ {A B : tp}, (product [A] [B]) ≅ [A × B].
Axiom def_rec : ∀ {F}, ▷ [F (rec F)] ≅ [rec F].

Notation lam := (intro def_arr).
Notation app := (elim def_arr).
Notation "lam: x ; e" := (lam (λ x, e)) (at level 100).
Infix "@" := app (at level 60).

Notation fold := (intro def_rec).
Notation unfold := (elim def_rec).
Notation "fold: e" := (fold e) (at level 100).
Notation "unfold: e" := (unfold e) (at level 100).

Notation pair := (intro def_prod).
Notation split := (elim def_prod).
Notation "⟨ e , e' ⟩" := (pair (Build_product e  e')).
Notation "fst: e" := (π1 (split e)) (at level 100).
Notation "snd: e" := (π2 (split e)) (at level 100).

Definition θ_arr_rhs {A B} (e : ▷ [A ⇒ B]) : [A ⇒ B] :=
  lam: x;
  θ: (λ f, f @ x) <$> e.

Definition θ_prod_rhs {A B} (e : ▷ [A × B]) : [A × B] :=
  ⟨ θ: (λ x, fst: x) <$> e, θ: (λ x, snd: x) <$> e ⟩.

Definition θ_rec_rhs {F} (e : ▷ [rec F]) : [rec F] :=
  fold: (θ ∘ unfold) <$> e.

Axiom θ_arr : ∀ {A B}, θ[A ⇒ B] = θ_arr_rhs.
Axiom θ_prod : ∀ {A B}, θ[A × B] = θ_prod_rhs.
Axiom θ_rec : ∀ {F}, θ[rec F] = θ_rec_rhs.


Axiom tt : [bool].
Axiom ff : [bool].
Axiom case : ∀ {A}, [bool] → [A] → [A] → [A].

Notation "case: b 'with' 'tt' ⇒ t | 'ff' ⇒ f 'end'" := (case b t f) (at level 100).
Notation "case[ A ]: b 'with' 'tt' ⇒ t | 'ff' ⇒ f 'end'" := (@case A b t f) (at level 100).

Axiom case_δ : ∀ {A} b t f, case[A]: (δ b) with tt ⇒ t | ff ⇒ f end = δ: case b t f.
Axiom case_tt : ∀ {A} t f, case[A]: tt with tt ⇒ t | ff ⇒ f end = t.
Axiom case_ff : ∀ {A} t f, case[A]: tt with tt ⇒ t | ff ⇒ f end = f.


Definition fixpoint {A} : [A ⇒ A] → [A] :=
  let w := λ h : [(rec: X; X ⇒ A) ⇒ A], h @ fold: next: lam: x; h @ x in
  λ f, w (lam: x; f @ w (lam: y; (θ: unfold x) @ y)).

Notation "fix: X ; F" := (fixpoint (lam (λ X, F))) (at level 100).

Definition bits := rec: X; bool × X.
Definition head : [bits ⇒ bool] := lam: xs; fst: θ: unfold: xs.
Definition tail : [bits ⇒ bits] := lam: xs; snd: θ: unfold: xs.

Definition ones : [bits] := fix: xs; fold: next: ⟨ tt, xs ⟩.

Definition bot {A} : [A] := fix: x; x.

Goal 0 ⊩ δ tt = bot.
  move=> boom; compute.
  rewrite ? beta θ_arr beta /Later.map Later.ap_compute.
  f_equal; apply: Later.from_eq.
  move: boom; by apply: Later.map.
Qed.

Goal case: δ: δ: tt with tt ⇒ ff | ff ⇒ tt end = δ: δ: ff.
  by rewrite ? case_δ case_tt.
Qed.

(* Every type defines a "functor of points". We would presumably be
   gluing along the functor A |-> Nv A. *)
Definition Nv A :=
  λ n,
  n ⊩ [A].

Definition Nv_action {A} : ∀ m n, m ≤ n → Nv A n → Nv A m.
  move=> m n mn a z.
  apply: a.
  apply: boom_leq; eauto.
Defined.
