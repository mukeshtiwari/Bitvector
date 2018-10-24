Require Import
        Coq.Vectors.Vector
        VectorLib.

Inductive Bit := Zero | One.

Definition And (x y : Bit) :=
  match x, y with
  | One, One => One
  | _, _ => Zero
  end.

Definition Or (x y : Bit) :=
  match x, y with
  | Zero, Zero => Zero
  | _, _ => One
  end.

Definition Bitflip (x : Bit) : Bit :=
  match x with
  | Zero => One
  | One => Zero
  end.

Lemma and_bit_flip : forall (x : Bit), And x (Bitflip x) = Zero.
Proof.
  refine (fun x => match x with
                | Zero => eq_refl
                | One => eq_refl
                end).
Qed.

Lemma bit_and_flip : forall (x : Bit), And (Bitflip x) x = Zero.
Proof.
  refine (fun x => match x with
                | Zero => eq_refl
                | One => eq_refl
                end).
Qed.



Definition Bitstream (n : nat) := Vector.t Bit n.

Fixpoint repeatN (n : nat) (x : Bit) : Bitstream n :=
  match n with
  | O => nil _
  | S n' => cons _ x _ (repeatN n' x)
  end.

   
Definition zipBits {n : nat} (f : Bit -> Bit -> Bit) (xs ys : Bitstream n) : Bitstream n :=
  zip_vectors f n xs ys.

Definition mapBits {n : nat} (f : Bit -> Bit) (xs : Bitstream n) : Bitstream n :=
  map_vector f n xs.

Definition appendBits {n m : nat} (xs : Bitstream n) (ys : Bitstream m) : Bitstream (n + m) :=
  append_vector n m xs ys.
  
(* All bits are zero *)
Definition allZero (n : nat) := repeatN n Zero. 

(* All bits are One *)
Definition allOne (n : nat) := repeatN n One.

Definition bitstreamAnd {n : nat} (xs ys : Bitstream n) : Bitstream n :=
  zipBits And xs ys.

Definition bistreamOr {n : nat} (xs ys : Bitstream n) : Bitstream n :=
  zipBits Or xs ys.


Definition bitstreamFlip {n : nat} (xs : Bitstream n) : Bitstream n :=
  mapBits Bitflip xs.

(* n is index. n = 0 means set the 0th bit *)
Fixpoint setBit {m : nat} (n : nat) : Bitstream (n + S m) -> Bitstream (n + S m).
  refine (match n as n' return n = n' -> Bitstream (n' + S m) -> Bitstream (n' + S m) with
          | O => fun H v => _
          | S n' => fun H v => _
          end eq_refl); inversion v.
  + exact (cons _ One _ H1).
  + exact (cons _ One _ (setBit _ _ H1)).
Defined.

Fixpoint fetchBit {m : nat} (n : nat) : Bitstream (n + S m) -> Bit.
  refine (match n as n' return n = n' -> Bitstream (n' + S m) -> Bit with
          | O => fun H v => _
          | S n' => fun H v => _
          end eq_refl); inversion v.
  + exact h.
  + exact (fetchBit _ _ H1).
Defined.                                         
  
Theorem  compliment_of_each_other :
  forall (n : nat) (xs : Bitstream n), bitstreamAnd xs (bitstreamFlip xs) = allZero n.
Proof.
  unfold Bitstream; unfold bitstreamAnd; unfold bitstreamFlip;
    unfold zipBits; unfold mapBits; unfold allZero.
  induction xs.
  + auto.
  + cbn. rewrite IHxs. rewrite and_bit_flip.
    auto.
Qed.


 
  
  
    
 
  
