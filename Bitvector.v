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


 
  
  
    
 
  
