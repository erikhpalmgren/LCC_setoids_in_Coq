(* 
   A collection of basic definitions and lemmas for Propositions-as-types at the Set level

  By Olov Wilander March 2012. 
  

*)

Require Import PropasTypesUtf8Notation.

(* This lemma may look silly, but it is not unusual to have
   Sigmas/Existentials nested the wrong way, and applying this lemma
   will let you proceed using tacticals, rather than having to give an
   entire term in one go. *)
Lemma sigrejig (A B: Set) (P: B → Set) (Q: (∃y, P y) → Set)
  : (∃y: B, ∃p: P y, Q (existT (λ y, P y) y p)) → ∃x: (∃y, P y), Q x.
Proof.
  intros [y [p Qyp]]. exists (existT (λ y, P y) y p); assumption.
Qed.

Lemma TTAC (A B: Type) (R: A → B → Type)
  : (∀x: A, ∃y: B, R x y) → ∃f: A → B, ∀x: A, R x (f x).
Proof.
  intro H. exists (λ a, projT1 (H a)). intro x; apply (projT2 (H x)).
Qed.

(* The identity type does not have unique proofs in general, but if
   identity is decidable, then proofs are unique.  This result is due
   to Hedberg. *)

(* !! Should notation for identity types be introduced?  Using perhaps
   ≊ or ≡ or ≐ or ≑ or some other symbol, and ⁻¹ and ⊙ and (what?). *)


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


Definition Identity_invlaw_l {A: Set} {a b: A} (p: Identity a b)
  : Identity (Identity_trans p (Identity_sym p)) (Identity_refl a)
  := Identity_rec A a (λ y: A, λ p: Identity a y,
                    Identity (Identity_trans p (Identity_sym p)) (Identity_refl a))
                 (Identity_refl (Identity_refl a)) b p.

Definition Identity_invlaw_r {A: Set} {a b: A} (p: Identity a b)
  : Identity (Identity_trans (Identity_sym p) p) (Identity_refl b)
  := Identity_rec A a (λ y: A, λ p: Identity a y,
                    Identity (Identity_trans (Identity_sym p) p) (Identity_refl y))
                 (Identity_refl (Identity_refl a)) b p.

Definition DecId (A: Set): Set := ∀x y: A, Identity x y ∨ ¬Identity x y.

Lemma Peano4 (n:nat): ¬Identity 0 (S n).
Proof.
  intro P.
  assert (TrueFalse (S n)) as H.
  apply tt.
  destruct P.
  apply H.
Defined.

Lemma nat_DecId: DecId nat.
Proof.
  intro m. induction m.
  intro y. induction y. left; split. right. 
  apply Peano4.
  
  intro y. destruct y. right. intro P.
  apply Peano4 with m. apply Identity_sym.
  apply P.

  specialize IHm with y. destruct IHm.
  left. apply Identity_congr; assumption.
  right. intro H; apply e. apply (Identity_congr pred (S m) (S y) H).
Defined.

Definition hedbergcon (A: Set) (z: A ∨ ¬A): A → A
  := λ a: A, match z with
              | inl x => x
              | inr _ => a
            end.
Definition hedbergiscon (A: Set) (z: A ∨ ¬A) (a a': A)
  : Identity (hedbergcon A z a) (hedbergcon A z a')
  := match z with
      | inl x => Identity_refl x
      | inr f => match (f a) with end
    end.
Definition hedbergcollapse (A: Set)
  (f: A → A) (fconst: ∀a a': A, Identity (f a) (f a'))
  (g: A → A) (gleftinv: ∀a: A, Identity (g (f a)) a)
  (a a': A): Identity a a'
  :=Identity_trans (Identity_sym (gleftinv a))
                   (Identity_trans (Identity_congr g _ _ (fconst a a')) (gleftinv a')).
Definition hedbergleftinv (A: Set) (nt: ∀x y: A, Identity x y → Identity x y)
  (a b: A): Identity a b → Identity a b
  := λ p, Identity_trans (Identity_sym (nt a a (Identity_refl a))) p.
Lemma hedbergisleftinv (A: Set) (nt: ∀x y: A, Identity x y → Identity x y)
  (a b: A) (p: Identity a b)
  : Identity (hedbergleftinv A nt a b (nt a b p)) p.
Proof.
  induction p. unfold hedbergleftinv. apply Identity_invlaw_r.
Defined.
Definition hedberg (A: Set) (deceq: ∀x y: A, Identity x y ∨ ¬Identity x y)
  : ∀x y: A, ∀p q: Identity x y, Identity p q
  := λ x y: A,
  hedbergcollapse
    (Identity x y)
    (hedbergcon (Identity x y) (deceq x y))
    (hedbergiscon (Identity x y) (deceq x y))
    (hedbergleftinv A (λ α β, hedbergcon (Identity α β) (deceq α β)) x y)
    (hedbergisleftinv A (λ α β, hedbergcon (Identity α β) (deceq α β)) x y).

  