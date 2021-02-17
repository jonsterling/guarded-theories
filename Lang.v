Require Import Unicode.Utf8 ssreflect.
Require Import GuardedLF.

(* This is a relatively simple theory of typed λ-calculus with
recursive types; every type is made to be an algebra for the later
modality. *)

Axiom tp : ◻.
Axiom tm : tp → Type.

Notation "⋆" := tp.
Notation "[ A ]" := (tm A).

Axiom bool : tp.
Axiom arr : tp → tp → tp.
Axiom rec : (tp → tp) → tp.

Infix "⇒" := arr (right associativity, at level 60).
Notation "rec: X ; B" := (rec (λ X, B)) (at level 100).

Axiom tt : [bool].
Axiom ff : [bool].
Axiom def_rec : ∀ {F}, ▷ [F (rec F)] ≅ [rec F].
Axiom def_arr : ∀ {A B}, ([A] → [B]) ≅ [A ⇒ B].
Axiom θ : ∀ {A}, ▷ [A] → [A].

Notation lam := (intro def_arr).
Notation app := (elim def_arr).
Notation fold := (intro def_rec).
Notation unfold := (elim def_rec).

Notation "fold: e" := (fold e) (at level 100).
Notation "unfold: e" := (unfold e) (at level 100).
Notation "θ: e" := (θ e) (at level 100).
Notation "θ[ A ]" := (@θ A).
Notation "lam: x ; e" := (lam (λ x, e)) (at level 100).
Infix "@" := app (at level 60).

Definition δ {A} : [A] → [A] :=
  θ ∘ next.

Definition θ_arr_rhs {A B} (e : ▷ [A ⇒ B]) : [A ⇒ B] :=
  lam: x;
  θ: (λ f, f @ x) <$> e.

Definition θ_rec_rhs {F} (e : ▷ [rec F]) : [rec F] :=
  fold: (θ ∘ unfold) <$> e.

Axiom θ_arr : ∀ {A B}, θ[A ⇒ B] = θ_arr_rhs.
Axiom θ_rec : ∀ {F}, θ[rec F] = θ_rec_rhs.

Definition fixpoint {A} : [A ⇒ A] → [A] :=
  let w := λ h : [(rec: X; X ⇒ A) ⇒ A], h @ fold: next: lam: x; h @ x in
  λ f, w (lam: x; f @ w (lam: y; (θ: unfold x) @ y)).

Definition bot {A} : [A] := fixpoint (lam: x; x).

Goal 0 ⊩ δ tt = bot.
  move=> boom; compute.
  rewrite ? beta θ_arr beta /Later.map Later.ap_compute.
  f_equal; apply: Later.from_eq.
  move: boom; by apply: Later.map.
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
