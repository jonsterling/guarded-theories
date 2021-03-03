Require Import Unicode.Utf8 ssreflect.
Require Import GuardedLF.
Require Import Logic.FunctionalExtensionality.

(* This is a relatively simple theory of typed CBPV λ-calculus with
recursive types; every type is made to be an algebra for the later
modality. *)

Axiom mode : ◻.
Axiom pos : mode.
Axiom neg : mode.

Axiom tp : mode → ◻.
Axiom tm : tp pos → Type.

Axiom bool : tp pos.
Axiom one : tp pos.
Axiom arr : tp pos → tp neg → tp neg.
Axiom prod : ∀ {μ}, tp μ → tp μ → tp μ.
Axiom coprod : tp pos → tp pos → tp pos.
Axiom rec : (tp neg → tp neg) → tp neg.
Axiom F : tp pos → tp neg.
Axiom U : tp neg → tp pos.

Notation "[ A ]" := (tm A).
Notation "⟪ A ⟫" := [ U A ].

Axiom bind : ∀ {A B}, [U (F A)] → ([A] → [U B]) → [U B].
Axiom ret : ∀ {A}, [A] → [U (F A)].
Notation "ret: e" := (ret e) (at level 100).

Infix "⇒" := arr (right associativity, at level 60).
Infix "&" := (@prod neg) (right associativity, at level 60).
Infix "⊗" := (@prod pos) (right associativity, at level 60).
Infix "⊕" := coprod (right associativity, at level 60).
Notation "rec: X ; B" := (rec (λ X, B)) (at level 100).

Axiom θ : ∀ {A}, ▶ [U A] → [U A].
Definition δ {A} (e : [U A]) : [U A] := θ (next e).

Notation "θ: e" := (θ e) (at level 100).
Notation "δ: e" := (δ e) (at level 100).
Notation "θ[ A ]" := (@θ A).
Notation "δ[ A ]" := (@δ A).

Axiom def_arr : ∀ {A B}, ([A] → [U B]) ≅ [U (A ⇒ B)].
Axiom def_prod_neg : ∀ {A B}, (product ⟪A⟫ ⟪B⟫) ≅ ⟪ A & B ⟫.
Axiom def_prod_pos : ∀ {A B}, (product [A] [B]) ≅ [A ⊗ B].
Axiom def_coprod : ∀ {A B}, (sum [A] [B]) ≅ [A ⊕ B].
Axiom def_rec : ∀ {H}, ▶ [U (H (rec H))] ≅ [U (rec H)].
Axiom def_one : True ≅ [one].

Notation lam := (intro def_arr).
Notation app := (elim def_arr).
Notation "lam: x ; e" := (lam (λ x, e)) (at level 100).
Infix "@" := app (left associativity, at level 50).

Notation fold := (intro def_rec).
Notation unfold := (elim def_rec).
Notation "fold: e" := (fold e) (at level 100).
Notation "unfold: e" := (unfold e) (at level 100).

Notation "pair-" := (intro def_prod_neg).
Notation "split-" := (elim def_prod_neg).
Notation "⟨ e , e' ⟩-" := (pair- (Build_product e  e')).
Notation "fst-: e" := (π1 (split- e)) (at level 100).
Notation "snd-: e" := (π2 (split- e)) (at level 100).

Notation "pair+" := (intro def_prod_pos).
Notation "split+" := (elim def_prod_pos).
Notation "⟨ e , e' ⟩+" := (pair+ (Build_product e  e')).
Notation "fst+: e" := (π1 (split+ e)) (at level 100).
Notation "snd+: e" := (π2 (split+ e)) (at level 100).


Notation "bind: x ← e ; k" := (bind e (λ x, k)) (at level 100).

Definition θ_arr_rhs {A B} (e : ▶ [U (A ⇒ B)]) : [U (A ⇒ B)] :=
  lam: x;
  θ: (λ f, f @ x) <$> e.

Definition θ_prod_rhs {A B} (e : ▶ [U (A & B)]) : [U (A & B)] :=
  ⟨ θ: (λ x, fst-: x) <$> e, θ: (λ x, snd-: x) <$> e ⟩-.

Definition θ_rec_rhs {H} (e : ▶ [U (rec H)]) : [U (rec H)] :=
  fold: (θ ∘ unfold) <$> e.

Axiom bind_ret : ∀ {A B} {x : [A]} {k : [A] → [U B]}, bind (ret x) k = k x.
Axiom θ_bind : ∀ {A B x k}, bind (θ[F A] x) k = θ[B] ((λ z, bind z k) <$> x).
Axiom θ_arr : ∀ {A B}, θ[A ⇒ B] = θ_arr_rhs.
Axiom θ_prod : ∀ {A B}, θ[A & B] = θ_prod_rhs.
Axiom θ_rec : ∀ {F}, θ[rec F] = θ_rec_rhs.

Axiom tt : [bool].
Axiom ff : [bool].
Axiom case : ∀ {A}, [bool] → [U A] → [U A] → [U A].

Notation "case: b 'with' 'tt' ⇒ t | 'ff' ⇒ f 'end'" := (case b t f) (at level 100).
Notation "case[ A ]: b 'with' 'tt' ⇒ t | 'ff' ⇒ f 'end'" := (@case A b t f) (at level 100).

Axiom case_tt : ∀ {A} t f, case[A]: tt with tt ⇒ t | ff ⇒ f end = t.
Axiom case_ff : ∀ {A} t f, case[A]: tt with tt ⇒ t | ff ⇒ f end = f.

Definition bits := rec: X; F (bool ⊗ U X).
Definition cons : ⟪ bool ⇒ U bits ⇒ bits ⟫ :=
  lam: x; lam: xs;
  fold: next: ret: ⟨x,xs⟩+.

Definition head : ⟪ U bits ⇒ F bool ⟫ :=
  lam: xs;
  bind: u ← θ: unfold: xs;
  ret: fst+: u.

Definition tail : ⟪ U bits ⇒ bits ⟫ :=
  lam: xs;
  bind: u ← θ: unfold: xs;
  snd+: u.

Ltac crush :=
  repeat
    (autorewrite with crush;
     autounfold with crush;
     simpl).

Hint Unfold θ_prod_rhs θ_rec_rhs θ_arr_rhs Later.map δ : crush.
Hint Rewrite @beta @θ_prod @θ_arr @θ_rec @Later.ap_compute @bind_ret @θ_bind : crush.

Goal ∀ x xs, head @ (cons @ x @ xs) = δ: ret x.
  move=> x xs.
  rewrite /head /cons.
  by crush.
Qed.


Goal ∀ x xs, tail @ (tail @ (cons @ x @ (cons @ x @ xs))) = δ: δ: xs.
  move=> x xs.
  rewrite /bits /tail /cons.
  by crush.
Qed.


Definition zeroes : ⟪ bits ⟫ :=
  fix: xs; cons @ ff @ θ: xs.

Lemma head_zeroes : head @ zeroes = δ: ret: ff.
  rewrite /head /zeroes /cons loeb_unfold.
  by crush.
Qed.

Lemma tail_cons : ∀ x xs, tail @ (cons @ x @ xs) = δ: xs.
  move=> x xs.
  rewrite /tail /cons /bits.
  by crush.
Qed.

Lemma tail_zeroes : tail @ zeroes = δ: δ: zeroes.
  rewrite /zeroes.
  rewrite {1} loeb_unfold.
  by rewrite tail_cons.
Qed.

Lemma tail_strict : ∀ xs, (tail @ δ: xs) = δ: tail @ xs.
  move=> xs.
  rewrite /tail /bits.
  by crush.
Qed.

Lemma head_strict : ∀ xs, (head @ δ: xs) = δ: head @ xs.
  move=> xs.
  rewrite /head /bits.
  by crush.
Qed.

Goal head @ (tail @ (tail @ zeroes)) = δ: δ: δ: δ: δ: ret ff.
  do 2 rewrite tail_zeroes ? tail_strict.
  rewrite ? head_strict.
  by rewrite head_zeroes.
Qed.


Definition bot {A} : ⟪ A ⟫ := fix: x; θ: x.

Goal 1 ⊩ (δ: δ: ret: tt) = bot.
  move=> z.
  rewrite /bot loeb_unfold -/bot /δ.
  f_equal.
  apply: Later.from_eq; move: z.
  apply: Later.pmap => z.
  rewrite /bot loeb_unfold -/bot /δ.
  f_equal.
  apply: Later.from_eq; move: z.
  by apply: Later.pmap.
Qed.

Fixpoint rep {A} (n : nat) (f : A → A) (x : A) : A :=
  match n with
  | 0 => x
  | S n => f (rep n f x)
  end.

Definition conat : tp neg := rec: X; F (one ⊕ U X).

Notation ax := (intro def_one I).

Definition ze : ⟪conat⟫ :=
  fold: next: ret: intro def_coprod (inl ax).

Definition su (n : ⟪conat⟫) : ⟪conat⟫ :=
  fold: next: ret: intro def_coprod (inr n).



Inductive wp_F {A : tp pos} (Φ : [A] → Prop) (H : ⟪F A⟫ → Prop) : ⟪F A⟫ → Prop :=
| wp_ret : ∀ e v, e = ret v → Φ v → wp_F Φ H e
| wp_step : ∀ e e', (e = δ: e') → H e' → wp_F Φ H e.


(* Weakest precondition *)
Definition wp {A : tp pos} (Φ : [A] → Prop) : ⟪F A⟫ → Prop :=
  fix: wp'; wp_F Φ (λ e, ⟨▷⟩ (wp' ⊛ next: e)).


Lemma wp_unfold {A : tp pos} {Φ : [A] → Prop} {e : ⟪F A⟫} : wp Φ e = wp_F Φ (fun e => ▷ (wp Φ e)) e.
Proof.
  rewrite /wp {1} loeb_unfold /Later.map.
  do ? f_equal; extensionality e'; f_equal.
  by rewrite Later.ap_compute Later.dlater_compute.
Qed.

Goal wp (λ v, v = tt) (head @ (cons @ tt @ zeroes)).
  rewrite wp_unfold; apply: wp_step.
  - by rewrite /head /cons; crush.
  - apply: pnext.
    rewrite wp_unfold.
    by apply: wp_ret.
Qed.

(* Only partial correctness ;-) *)
Goal wp (λ v, v = tt) bot.
  apply: ploeb => L.
  rewrite wp_unfold; apply: wp_step; eauto.
  by rewrite /bot {1} loeb_unfold.
Qed.
