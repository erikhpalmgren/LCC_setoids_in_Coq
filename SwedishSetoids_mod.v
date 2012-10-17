(*
   Swedish style setoids, under propositions-as-types.
*)

Require Import PropasTypesUtf8Notation PropasTypesBasics_mod.

Record setoid: Type :=
  {
    setoidbase :> Set;
    setoideq   :  setoidbase → setoidbase → Set;
    setoidrefl :  ∀x, setoideq x x;
    setoidsym  :  ∀x y, setoideq x y → setoideq y x;
    setoidtra  :  ∀x y z, setoideq x y → setoideq y z → setoideq x z
  }.

Notation "x ≈ y" := (setoideq _ x y) (at level 70, no associativity, only parsing).
Notation "x ≈,{ A  } y" := (setoideq A x y) (at level 70, no associativity).
Notation "x ≈[ A ] y" := (setoideq A x y) (at level 70, no associativity, only parsing).

Hint Resolve setoidrefl : swesetoid.
Hint Immediate setoidsym : swesetoid.
Hint Resolve setoidtra : swesetoid. (* The warning here is expected *)

Ltac swesetoid := simpl; eauto with swesetoid.


Record Setoid: Type :=
  {
    Setoidbase :> Type;
    Setoideq   :  Setoidbase → Setoidbase → Set;
    Setoidrefl :  ∀x, Setoideq x x;
    Setoidsym  :  ∀x y, Setoideq x y → Setoideq y x;
    Setoidtra  :  ∀x y z, Setoideq x y → Setoideq y z → Setoideq x z
  }.

Notation "x ≈≈ y" := (Setoideq _ x y) (at level 70, no associativity, only parsing).
Notation "x ≈≈,{ A  } y" := (Setoideq A x y) (at level 70, no associativity).
Notation "x ≈≈[ A ] y" := (Setoideq A x y) (at level 70, no associativity, only parsing).

Record Typeoid: Type :=
  {
    Typeoidbase :> Type;
    Typeoideq   :  Typeoidbase → Typeoidbase → Type;
    Typeoidrefl :  ∀x, Typeoideq x x;
    Typeoidsym  :  ∀x y, Typeoideq x y → Typeoideq y x;
    Typeoidtra  :  ∀x y z, Typeoideq x y → Typeoideq y z → Typeoideq x z
  }.

Notation "x ≈≈≈ y" := (Typeoideq _ x y) (at level 70, no associativity, only parsing).
Notation "x ≈≈≈,{ A  } y" := (Typeoideq A x y) (at level 70, no associativity).
Notation "x ≈≈≈[ A ] y" := (Typeoideq A x y) (at level 70, no associativity, only parsing).

Record setoidmap (A B: setoid) :=
  {
    setoidmapfunction :> A → B;
    setoidmapextensionality : ∀x y: A, x ≈ y → setoidmapfunction x ≈ setoidmapfunction y
  }.

Hint Resolve setoidmapextensionality : swesetoid.

Definition setoidmaps (A B: setoid): setoid.
apply (Build_setoid (setoidmap A B) (λ f g, ∀x:A, f x ≈ g x)); swesetoid.
Defined.

Notation "A ⇒ B" := (setoidmaps A B) (at level 55, right associativity).

Lemma binsetoidmap_helper {A B C: setoid} (f:A → B → C)
  (p: ∀a a', a ≈ a' → ∀b, f a b ≈ f a' b)
  (q: ∀a b b', b ≈ b' → f a b ≈ f a b')
  : A ⇒ B ⇒ C.
Proof.
  apply (Build_setoidmap A (B ⇒ C) (λ a, (Build_setoidmap B C (f a) (q a))) p).
Defined.

Lemma trinsetoidmap_helper {A B C D: setoid} (f: A → B → C → D)
  (p: ∀a a', a ≈ a' → ∀b c, f a b c ≈ f a' b c)
  (q: ∀a b b', b ≈ b' → ∀c, f a b c ≈ f a b' c)
  (r: ∀a b c c', c ≈ c' → f a b c ≈ f a b c')
  : A ⇒ B ⇒ C ⇒ D.
Proof.
  apply (Build_setoidmap A (B ⇒ C ⇒ D)) with (λ a, binsetoidmap_helper (f a) (q a) (r a));
    assumption.
Defined.

Definition idmap {A: setoid}: setoidmap A A.
apply (Build_setoidmap A A (λ x: A, x)); swesetoid.
Defined.

Definition comp {A B: setoid} (C: setoid): (B ⇒ C) ⇒ (A ⇒ B) ⇒ (A ⇒ C).
apply trinsetoidmap_helper with (λ f: B ⇒ C, λ g: A ⇒ B, λ a, f (g a));
  swesetoid.
Defined.

Notation "F ∘ G" := (comp _ F G) (at level 10).

Theorem setoidmap_composition_assoc {A B C D: setoid} (F: C ⇒ D) (G: B ⇒ C) (H: A ⇒ B)
  : F ∘ G ∘ H ≈ F ∘ (G ∘ H).
Proof.
  swesetoid.
Qed.

Theorem setoidmap_comp_id_left {A B: setoid} (F: A ⇒ B): idmap ∘ F ≈ F.
Proof.
  swesetoid.
Qed.

Theorem setoidmap_comp_id_right {A B: setoid} (F: A ⇒ B): F ∘ idmap ≈ F.
Proof.
  swesetoid.
Qed.

(* This redefined identity types for Set 


Inductive Identity {A: Set}(x: A) : A -> Set :=
Identity_refl : Identity x x.

Theorem Identity_congr {A B: Set}(f:A -> B)(x y:A):
Identity x y -> Identity (f x) (f y).
Proof.
  intro P.  
  destruct P.
  apply (Identity_refl (f x)).
Defined.

Definition Identity_trans  {A: Set}{a b c:A}: 
Identity a b -> Identity b c -> Identity a c.
  intros p q.
  destruct p.
  apply q.
Defined.

Definition Identity_sym  {A: Set}{a b:A}: 
Identity a b -> Identity b a.
  intros p.
  destruct p.
  apply (Identity_refl a).
Defined.


Definition TrueFalse (n:nat): Set :=
  match n with 
    | 0   => ⊥
    | S _ => ⊤
  end.
*)

(* Some particular setoids *)

Definition empty_setoid: setoid.
apply (Build_setoid ⊥ (λ x y, ⊥)); trivial.
Defined.

Definition unit_setoid: setoid.
apply (Build_setoid ⊤ (λ x y, ⊤)); trivial.
Defined.

Definition nat_setoid: setoid.
apply (Build_setoid ℕ (λ x y, Identity x y)).
apply Identity_refl.
intros x y. apply Identity_sym.
intros x y z. apply Identity_trans.
Defined.

Definition sum_setoid (A B: setoid): setoid.
apply (Build_setoid (A + B)
  (λ a b, match a with
            | inl α => match b with
                        | inl α' => α ≈ α'
                        | inr _  => ⊥
                      end
            | inr β => match b with
                        | inl _  => ⊥
                        | inr β' => β ≈ β'
                      end
          end)).
intros []; swesetoid.
intros [] []; swesetoid.
intros [] [] []; swesetoid; try contradiction.
Defined.

Notation "x ⊕ y" := (sum_setoid x y) (at level 40). 

Definition inl_setoid {A B: setoid}: A ⇒ A ⊕ B.
apply (Build_setoidmap _ (A ⊕ B) (λ a: A, inl B a)).
auto.
Defined.

Definition inr_setoid {A B: setoid}: B ⇒ A ⊕ B.
apply (Build_setoidmap _ (A ⊕ B) (λ b: B, inr A b)).
auto.
Defined.

Definition sum_mediating {A B: setoid} (X: setoid) (f: A ⇒ X) (g: B ⇒ X)
  : A ⊕ B ⇒ X.
apply (Build_setoidmap (A ⊕ B) X
  (λ x, match x with
          | inl a => f a
          | inr b => g b
        end)).
intros [a | b] [a' | b'] p; try contradiction p;
  apply setoidmapextensionality; assumption.
Defined.

Lemma sum_universality {A B: setoid} (X: setoid) (f: A ⇒ X) (g: B ⇒ X)
  : f ≈ sum_mediating X f g ∘ inl_setoid
  ∧ g ≈ sum_mediating X f g ∘ inr_setoid
  ∧ ∀h, f ≈ h ∘ inl_setoid → g ≈ h ∘ inr_setoid → sum_mediating X f g ≈ h.
Proof.
  repeat split; try (intro; apply setoidrefl).
  intros h feq geq [a | b]; simpl. apply feq. apply geq.
Qed.

Definition sum_map {A B C D: setoid} (f: A ⇒ C) (g: B ⇒ D): A ⊕ B ⇒ C ⊕ D
  := sum_mediating (C ⊕ D) (inl_setoid ∘ f) (inr_setoid ∘ g).

Definition prod_setoid (A B: setoid): setoid.
apply (Build_setoid (A ∧ B)
  (λ p q, let (a,b) := p in let (c,d) := q in a ≈ c ∧ b ≈ d)).
intros []; swesetoid.
intros [] [] []; swesetoid.
intros [] [] [] [] []; swesetoid.
Defined.

Notation "x ⊗ y" := (prod_setoid x y) (at level 30).

Definition fst_setoid {A B: setoid}: A ⊗ B ⇒ A.
apply (Build_setoidmap (A ⊗ B) A (λ p, match p with (a,b) => a end)).
intros [x _] [y _] [p _]; auto.
Defined.

Definition snd_setoid {A B: setoid}: A ⊗ B ⇒ B.
apply (Build_setoidmap (A ⊗ B) B (λ p, match p with (_, b) => b end)).
intros [_ x] [_ y] [_ p]; auto.
Defined.

Definition prod_mediating {A B: setoid} (X: setoid) (f: X ⇒ A) (g: X ⇒ B)
  : X ⇒ A ⊗ B.
apply (Build_setoidmap X (A ⊗ B) (λ x, (f x, g x))).
intros; split; apply setoidmapextensionality; assumption.
Defined.

Lemma prod_universality {A B: setoid} (X: setoid) (f: X ⇒ A) (g: X ⇒ B)
  : f ≈ fst_setoid ∘ (prod_mediating X f g)
  ∧ g ≈ snd_setoid ∘ (prod_mediating X f g)
  ∧ ∀h, f ≈ fst_setoid ∘ h → g ≈ snd_setoid ∘ h → prod_mediating X f g ≈ h.
Proof.
  repeat split; try (intro; apply setoidrefl).
  intros h feq geq x. simpl. rewrite (surjective_pairing (h x)).
  split. apply feq. apply geq.
Qed.

Definition prod_map {A B C D: setoid} (f: A ⇒ C) (g: B ⇒ D): A ⊗ B ⇒ C ⊗ D
  := prod_mediating (A ⊗ B) (f ∘ fst_setoid) (g ∘ snd_setoid).

Definition ExtId (A: setoid) (x y: A): setoid.
apply (Build_setoid (x ≈ y) (λ _ _, ⊤)); split.
Defined.

(* Now we aim to construct coequalizers in the E-category of setoids *)

(* First the reflexive and transitive closure of a relation on a setoid. *)
Definition RTclosure {A: setoid} (R: A → A → Set)
  := λ (x y: A), ∃f: ℕ → A, ∃n: ℕ, x ≈ f 0 ∧ f n ≈ y ∧ ∀m: ℕ, R (f m) (f (S m)).

(* We end up needing some basic arithmetic - but want to stay in Set, and use
   the identity type rather than Coq's standard equality = / eq *)

Lemma zero_right: ∀x: ℕ, Identity x (x + 0).
Proof.
  induction x. apply Identity_refl. simpl; apply Identity_congr. assumption.
Defined.

Lemma add_suc: ∀x y: ℕ, Identity (S x + y) (x + S y).
Proof.
  intros. induction x.
  apply Identity_refl.
  change (Identity (S (S x + y)) (S (x + S y))).
  apply Identity_congr. assumption.
Defined.

Lemma add_subtract_cancellation: ∀x y: ℕ, Identity x ((x + y) - y).
Proof.
  induction y.
  destruct x. apply Identity_refl. simpl; apply Identity_congr. apply zero_right.
  destruct x. assumption. simpl. destruct (add_suc x y). assumption.
Defined.

Fixpoint le (x y: ℕ): bool
  := match (x, y) with
      | (0, _) => true
      | (S _, 0) => false
      | (S m, S n) => le m n
    end.

Notation "x ≤ y" := (Identity true (le x y)) (at level 70).
Notation "x > y" := (Identity false (le x y)) (at level 70).


Definition Bool2TrueFalse (b:bool): Set :=
  match b with 
    | false   => ⊥
    | true => ⊤
  end.


Lemma le_Sn_0_not (x: ℕ): ¬ (S x)  ≤ 0. 
Proof.
  intro P.
  assert (Bool2TrueFalse (le (S x) 0)) as H.
  destruct P.
  apply tt.
  apply H.
Defined.

Lemma le_refl (x: ℕ): x ≤ x.
Proof.
  induction x. apply Identity_refl. assumption.
Defined.

Lemma le_trans (x: ℕ)
  : ∀y z, x ≤ y → y ≤ z → x ≤ z.
Proof.
  induction x.
  intros; apply Identity_refl.
  destruct y.
  intros z H H1.
  assert  ⊥ as H2.
  apply (le_Sn_0_not x).
  assumption.
  destruct H2.
  intro z.
  induction z.
  intros H H1.
  assert  ⊥ as H2.
  apply (le_Sn_0_not y).
  assumption.
  destruct H2.
  intros H1 H2.
  simpl.
  simpl in H1.
  simpl in H2.
  apply (IHx y z).
  assumption.
  assumption.
Defined.

Lemma gt_trans
  : ∀x y z: ℕ, x > y → y > z → x > z.
Proof.
  induction x.
  intros y z H H1.
  assert  ⊥ as H2.
  assert (Bool2TrueFalse (le 0 y)) as H3.
  simpl.
  apply tt.
  destruct  H.
  apply H3.
  destruct H2.
  destruct y.
  intros z H1 H2.
  assert (Bool2TrueFalse (le 0 z)) as H3.
  simpl.
  apply tt.
  destruct H2. 
  destruct H3.
  intro z.
  destruct z.
  intros H1 H2.
  simpl.
  apply (Identity_refl false).
  intros H1 H2.
  simpl.
  simpl in H1.
  simpl in H2. 
  apply (IHx y z).
  assumption.
  assumption.
Defined.


Lemma le_antisym
  : ∀x y: ℕ, x ≤ y → y ≤ x -> Identity x y.
Proof.
  induction x. destruct y.
  intros; apply (Identity_refl 0).
  intros H1 H2.
  assert ⊥ as H3.
  apply (le_Sn_0_not y).
  assumption.
  destruct H3.
  intro y. destruct y.
   intros H1 H2.
  assert ⊥ as H3.
  apply (le_Sn_0_not x).
  assumption.
  destruct H3.
  intros H1 H2.
  simpl in H1.
  simpl in H2.
  apply Identity_congr.
  apply IHx.
  assumption.
  assumption.
Defined.

Lemma le_suc: ∀x y: ℕ, x ≤ y → x ≤ S y.
Proof.
  induction x.
  intros; apply Identity_refl.
  destruct y.  intros H1.
  assert ⊥ as H3.
  apply (le_Sn_0_not x).
  assumption.
  destruct H3.
  apply IHx.
Defined.

Lemma le_pred: ∀x y, S x ≤ y → x ≤ y.
Proof.
  induction y. intros H1.
  assert ⊥ as H3.
  apply (le_Sn_0_not x).
  assumption.
  destruct H3.
  simpl. apply le_suc.
Defined.

Lemma gt_suc (x: ℕ): S x > x.
Proof.
  induction x. apply Identity_refl. assumption.
Defined.

Lemma gt_suc_le: ∀x y: ℕ, x > y → S y ≤ x.
Proof.
  induction x.
  intros y H.
 assert  ⊥ as H2.
  assert (Bool2TrueFalse (le 0 y)) as H3.
  simpl.
  apply tt.
  destruct H.
  assumption.
  destruct H2.
  destruct y.
  intro; apply Identity_refl.
  apply IHx.
Defined.

Lemma gt_suc_sum (x y: ℕ): S x + y > y.
Proof.
  induction x. simpl plus. apply gt_suc.
  apply gt_trans with (S x + y). apply gt_suc. assumption.
Defined.

Lemma suc_subtract: ∀x y: ℕ, y ≤ x → Identity (S (x - y)) (S x - y).
Proof.
  induction x.
  destruct y. intro; apply Identity_refl.
  intro H.
  assert ⊥ as H3.
  apply (le_Sn_0_not y).
  assumption.
  destruct H3.
  intro y.
  destruct y.
  intro H.
  apply Identity_refl.
  intro H2.
  simpl.
  apply IHx.
  simpl in H2.
  assumption.
Defined.

Lemma add_subtract_assoc: ∀x y z: ℕ, z ≤ y → Identity (x + (y - z)) (x + y - z).
Proof.
  induction x.
  intros; apply Identity_refl.
  intros.
  destruct (Identity_sym (add_suc x (y - z))).
  destruct (Identity_sym (suc_subtract y z H)).
  destruct (Identity_sym (add_suc x y)).
  apply IHx. apply le_suc; assumption.
Defined.

Lemma sub_cutoff: ∀x y: ℕ, x ≤ y → Identity 0 (x - y).
Proof.
  induction x.
  intros; apply Identity_refl.
  intro y; case y.
   intro H.
  assert ⊥ as H3.
  apply (le_Sn_0_not x).
  assumption.
  destruct H3.  apply IHx.
Defined.

Lemma rtclosure_trans {A: setoid} (R: A → A → Set)
  (Rextl: ∀x y z: A, x ≈ y → R x z → R y z)
  : ∀x y z: A, RTclosure R x y → RTclosure R y z → RTclosure R x z.
Proof.
  intros x y z [f [m [ef0 [em fp]]]] [g [n [eg0 [en gp]]]].
  exists (λ a: ℕ, if (le a m) then (f a) else (g (a - m))).
  exists (n + m).
  split. simpl; assumption.
  split.
  destruct n. simpl. destruct (le_refl m). swesetoid.
  destruct (gt_suc_sum n m). destruct (add_subtract_cancellation (S n) m). assumption.
  intro k.
  assert (bool_dec: ((S k) ≤ m) + ((S k) > m)).
  destruct (le (S k) m); [left | right]; apply Identity_refl.
  destruct bool_dec as [i | i].
  destruct (le_pred k m i). destruct i. apply fp.
  assert (bool_dec: (k ≤ m) + (k > m)).
  destruct (le k m); [left | right]; apply Identity_refl.
  destruct bool_dec as [j | j].
  assert (eq: Identity m k).
  apply le_antisym. apply (gt_suc_le (S k) m i). assumption.
  destruct i. destruct j. destruct eq.
  apply Rextl with (g 0). swesetoid.
  assert (eq: Identity 1 (S m - m)). change (Identity 1 (1 + m - m)).
  apply add_subtract_cancellation. destruct eq. apply gp.
  assert (eq: Identity (S (k - m)) (S k - m)). apply suc_subtract.
  apply (gt_suc_le (S k) m i).
  destruct i. destruct j. destruct eq. apply gp.
Defined.

Lemma RTclosure_preserve_sym {A: setoid} (R: A → A → Set)
  (Rsym: ∀x y: A, R x y → R y x)
  (Rrefl: ∀x: A, R x x)
  : ∀x y: A, RTclosure R x y → RTclosure R y x.
Proof.
  intros x y [f [m [ef0 [em fp]]]].
  exists (λ n: ℕ, f (m - n)).
  exists m.
  split.
  assert (eq: Identity m (m - 0)).
  case m; intros; apply Identity_refl.
  destruct eq; swesetoid.
  split.
  assert (eq: Identity 0 (m - m)). clear em.
  induction m. apply Identity_refl. simpl. assumption.
  destruct eq. swesetoid.
  intro k.
  assert (bool_dec: (m > k) + (m ≤ k)).
  destruct (le m k); [right | left]; apply Identity_refl.
  destruct bool_dec.
  change (m - k) with (S m - S k).
  destruct (suc_subtract m (S k) (gt_suc_le m k i)).
  apply Rsym. apply fp.
  destruct (sub_cutoff m k i).
  destruct (sub_cutoff m (S k) (le_suc m k i)).
  apply Rrefl.
Defined.

Lemma RTclosure_preserve_refl {A: setoid} (R: A → A → Set)
  (Rrefl: ∀x: A, R x x)
  : ∀x: A, RTclosure R x x.
Proof.
  intro x.
  exists (λ n, x).
  exists 0.
  repeat split; try swesetoid.
Defined.

Definition coequalizer_setoid {A B: setoid} (f g: A ⇒ B): setoid.
apply
  (Build_setoid B
    (RTclosure
      (λ x y, x ≈ y ∨ (∃a: A, f a ≈ x ∧ g a ≈ y) ∨ (∃a: A, f a ≈ y ∧ g a ≈ x)))).
apply RTclosure_preserve_refl. swesetoid.
apply RTclosure_preserve_sym.
intros x y [e | [[a [e1 e2]] | [a [e1 e2]]]]; swesetoid. swesetoid.
apply rtclosure_trans.
intros x y z e [e' | [[a [e1 e2]] | [a [e1 e2]]]]; swesetoid.
right; left; swesetoid.
right; right; swesetoid.
Defined.

Definition coequalizer_map {A B: setoid} (f g: A ⇒ B): B ⇒ coequalizer_setoid f g.
apply (Build_setoidmap B (coequalizer_setoid f g) (λ b, b)).
intros. exists (λ n, x). exists 0. repeat split; swesetoid.
Defined.

Lemma coequalizer_eq {A B: setoid} (f g: A ⇒ B)
  : (coequalizer_map f g) ∘ f ≈ (coequalizer_map f g) ∘ g.
Proof.
  intro a. simpl.
  exists (nat_rec (λ _, B) (f a) (λ _ _, g a)). exists 1.
  repeat split; swesetoid.
  intro k; case k; simpl.
  right; left; swesetoid.
  intro; left; swesetoid.
Defined.

Lemma coequalizer_universal {A B C: setoid} (f g: A ⇒ B) (h: B ⇒ C)
  : h ∘ f ≈ h ∘ g → ∃m: (coequalizer_setoid f g) ⇒ C, h ≈ m ∘ (coequalizer_map f g).
Proof.
  intro heq.
  assert (mext: ∀x y: coequalizer_setoid f g, x ≈ y → h x ≈ h y).
  intros x y [φ [n [e0 [en p]]]].
  assert (claim: ∀m: ℕ, h x ≈ h (φ m)).
  induction m. swesetoid.
  apply setoidtra with (h (φ m)). apply IHm.
  destruct p with m as [e | [[a [e1 e2]] | [a [e1 e2]]]].
  swesetoid.
  apply setoidtra with (h (f a)). swesetoid.
  apply setoidtra with (h (g a)). apply (heq a). swesetoid.
  apply setoidtra with (h (g a)). swesetoid.
  apply setoidtra with (h (f a)). apply setoidsym. apply (heq a). swesetoid.
  apply setoidtra with (h (φ n)); swesetoid.
  exists (Build_setoidmap (coequalizer_setoid f g) C (λ x, h x) mext).
  simpl. swesetoid.
Defined.

(* Fin *)
