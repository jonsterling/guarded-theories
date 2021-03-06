Require Import Unicode.Utf8 ssreflect.
Require Import micromega.Lia.

Set Primitive Projections.

Record iso (A B : Type) :=
  {intro : A → B;
   elim : B → A;
   eta : ∀ x, intro (elim x) = x;
   beta : ∀ x, elim (intro x) = x}.

Arguments intro [_] [_] _.
Arguments elim [_] [_] _.

Record product (A B : Type) :=
  {π1 : A;
   π2 : B}.

Arguments Build_product [_] [_] _ _.
Arguments π1 [_] [_] _.
Arguments π2 [_] [_] _.

Infix "≅" := iso (at level 100).
Notation "◻" := Type.
Notation "f ∘ g" := (λ x, f (g x)) (at level 10).

Axiom later : Type → Type.
Notation "▶ A" := (later A) (at level 60).

Axiom dlater : ▶ Prop → Prop.
Notation "⟨▷⟩ A" := (dlater A) (at level 60).

Axiom plater : Prop → Prop.
Notation "▷ A" := (plater A) (at level 60).

Axiom next : ∀ {A}, A → ▶ A.
Axiom pnext : ∀ {P : Prop}, P → ▷ P.
Notation "next: x" := (next x) (at level 100).

Axiom loeb : ∀ {A}, (▶ A → A) → A.
Axiom ploeb : ∀ {A : Prop}, (▷ A → A) → A.
Notation "fix: x ; e" := (loeb (λ x, e)) (at level 100).
Axiom loeb_unfold : ∀ {A f}, @loeb A f = f (next (loeb f)).

Module Later.
  Axiom from_eq : ∀ {A} (a b : A), ▷ (a = b) → next a = next b.
  Axiom to_eq : ∀ {A} (a b : A), next a = next b → ▷ (a = b).
  Axiom ap : ∀ {A B}, later (A → B) → later A → later B.
  Axiom pap : ∀ {A B : Prop}, plater (A → B) → plater A → plater B.

  Axiom dlater_compute : ∀ A, ⟨▷⟩ (next A) = ▷ A.


  Module ApNotation.
    Infix "⊛" := ap (at level 50).
    Infix "⊛p" := pap (at level 50).
  End ApNotation.

  Import ApNotation.

  Axiom ap_compute : ∀ {A B} (f : A → B) (x : A), next f ⊛ next x = next (f x).

  Definition map {A B} : (A → B) → later A → later B :=
    fun f x => next f ⊛ x.

  Definition pmap {A B : Prop} : (A → B) → plater A → plater B :=
    fun f x => pnext f ⊛p x.
End Later.

Export Later.ApNotation.
Infix "<$>" := Later.map (at level 50).

Fixpoint boom n :=
  ▷ match n with
    | 0 => False
    | S n => boom n
    end.

Notation "n ⊩ P" := (boom n → P) (at level 100).


Lemma boom_suc : ∀ n, boom n → boom (S n).
Proof.
  move=> n.
  apply: pnext.
Qed.

Lemma boom_leq : ∀ m n, m ≤ n → boom m → boom n.
Proof.
  move=> m; elim.
  - move=> ?.
    replace m with 0; first by auto.
    by lia.
  - move=> n ih p z.
    compare m (S n).
    + by move=> <- .
    + move=> q.
      apply: pnext; apply: ih; last by auto.
      by lia.
Defined.
