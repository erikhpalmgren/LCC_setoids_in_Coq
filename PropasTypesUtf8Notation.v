(* Author: Olov Wilander 2012

   Some Utf8 notations for Propositions-as-types at the Set level.
   
   N.B. Many of these notations conflict with the standard use in the
   Utf8 and Utf8_core modules, where they are used at the Prop level.
*)

(* This is probably not compatible with the bounded quantifiers
Notation "∀ x .. y , P" := (forall x, .. (forall y, P) ..)
  (at level 200, x binder, y binder, right associativity) : type_scope.
Notation "∃ x .. y , P" := (sigT (fun x => .. (sigT (fun y => P)) ..))
  (at level 200, x binder, y binder, right associativity) : type_scope.
*)
Notation "∀ x , P" := (forall x, P)
  (at level 200, x at level 0, right associativity) : type_scope.
Notation "∀ x y , P" := (forall x y, P)
  (at level 200, x, y at level 0, right associativity) : type_scope.
Notation "∀ x y z , P" := (forall x y z, P)
  (at level 200, x, y, z at level 0, right associativity) : type_scope.
Notation "∀ x y z w , P" := (forall x y z w, P)
  (at level 200, x, y, z, w at level 0, right associativity) : type_scope.
Notation "∀ x : X , P" := (forall x: X, P)
  (at level 200, x at level 0, right associativity) : type_scope.
Notation "∀ x y : X , P" := (forall x y: X, P)
  (at level 200, x, y at level 0, right associativity) : type_scope.
Notation "∀ x y z : X , P" := (forall x y z: X, P)
  (at level 200, x, y, z at level 0, right associativity) : type_scope.
Notation "∃ x , P" := (sigT (fun x => P))
  (at level 200, x at level 0, right associativity) : type_scope.
Notation "∃ x : y , P" := (sigT (fun x: y => P))
  (at level 200, x at level 0, right associativity) : type_scope.

Notation "x ∨ y" := (sum x y) (at level 85, right associativity) : type_scope.
Notation "x ∧ y" := (prod x y) (at level 80, right associativity) : type_scope.
Notation "x → y" := (x -> y) (at level 90, right associativity) : type_scope.
Notation "x ↔ y" := ((x → y) ∧ (y → x)) (at level 95, no associativity) : type_scope.
Notation "⊥" := (Empty_set) : type_scope.
Notation "⊤" := (unit) : type_scope.
Notation "¬ x" := (x → ⊥) (at level 75) : type_scope.
Notation "x ≠ y" := (¬(x = y)) (at level 70) : type_scope.

Notation "'λ' x .. y , t" := (fun x => .. (fun y => t) ..) (at level 200, x binder, y binder, right associativity).

Notation ℕ := nat.

(* End Of File *)