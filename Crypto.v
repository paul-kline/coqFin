(** 
Perfect Crypto - Simple definitions for message encryption and signing using
symmetric and assymetric keys

Perry Alexander
The University of Kansas

Provides definitions for:

- [keyType] - [symmetric], [public] and [private] key constructors.
- [inverse] - defines the inverse of any key.
- [is_inverse] - proof that [inverse] is decidable and provides a decision procesure for [inverse].
- [is_not_decryptable] - predicate indicating that a message is or is not decryptable using a specified key.
- [decrypt] - attempts to decrypt a message with a given key.  Returns the decrypted message if decryption occurs.  Returns a proof that the message cannot be decrypted with the key if decryption does not occur.
- [is_signed] - proof that signature checking is decidable and provides a decision procedure for signature check.
- [check] - checks a signature on a message with a given key.  Returns a proof that the check succeeds or does not succeed.
- [check_dec] - proof that signature checking is decidable and provides a decision procedure for signature checking.  Alternative function for [check].
*)

Require Import Omega.

(** Key values will be [nat] *)

Definition key_val : Type := nat.

(** Key types are [symmetric], [public] and [private]. *)
Inductive keyType: Type :=
| symmetric : key_val -> keyType
| private : key_val -> keyType
| public : key_val -> keyType.

(** A [symmetric] key is its own inverse.  A [public] key is the inverse of
  the [private] key with the same [key_val].  A [private] key is the inverse of
  the [public] key with the same [key_val]. *)

Fixpoint inverse(k:keyType):keyType :=
match k with
| symmetric k => symmetric k
| public k => private k
| private k => public k
end.

(** Proof that inverse is decidable for any two keys. The resulting proof
 gives us the function [is_inverse] that is a decision procedure for key 
 inverse checking.  It will be used in [decrypt] and [check] later in the
 specification. *)
Theorem is_inverse:forall k k', {k = (inverse k')}+{k <> (inverse k')}.
Proof.
  intros.
  destruct k; destruct k'.
  destruct (eq_nat_dec k k0) as [Hinv | Hninv].
    left. simpl. auto.
    right. simpl. unfold not. intros. inversion H. contradiction.
  right; simpl; unfold not; intros; inversion H.
  right. simpl. unfold not. intros. inversion H.
  right. simpl. unfold not. intros. inversion H.
  right. simpl. unfold not. intros. inversion H.
  destruct (eq_nat_dec k k0) as [Hinv | Hninv].
    left. simpl. auto.
    right. simpl. unfold not. intros. inversion H. contradiction.
  right. simpl. unfold not. intros. inversion H.
  destruct (eq_nat_dec k k0) as [Hinv | Hninv].
    left. simpl. auto.
    right. simpl. unfold not. intros. inversion H. contradiction.
  right. simpl. unfold not. intros. inversion H.
Defined.

Eval compute in (is_inverse (public 1) (private 1)).

Eval compute in (is_inverse (public 1) (private 2)).

Eval compute in (is_inverse (public 2) (private 1)).

Eval compute in (is_inverse (private 1) (public 1)).

Eval compute in (is_inverse (symmetric 1) (symmetric 1)).

Eval compute in (is_inverse (symmetric 1) (symmetric 2)).

(** Various proofs for keys and properties of the inverse operation.  All keys
  must have an inverse.  All keys have a unique inverse.  Equal inverses come
  from equal keys *)

Theorem inverse_injective : forall k1 k2, inverse k1 = inverse k2 -> k1 = k2.
Proof.
  intros.
  destruct k1; destruct k2; simpl in H; try (inversion H); try (reflexivity).
Qed.

Hint Resolve inverse_injective.

Theorem inverse_inverse : forall k, inverse (inverse k) = k.
Proof.
  intros. destruct k; try reflexivity.
Qed.

Hint Resolve inverse_inverse.

Theorem inverse_surjective : forall k, exists k', (inverse k) = k'.
Proof.
  intros. exists (inverse k). auto.
Qed.

Hint Resolve inverse_surjective.

Theorem inverse_bijective : forall k k',
    inverse k = inverse k' ->
    k = k' /\ forall k, exists k'', inverse k = k''.
Proof.
  auto.
Qed.

(** Basic messages held abstract.  Compound messages are keys, encrypted and
  signed messages, hashes and pairs. *) 

Inductive message(basicType:Type) : Type :=
| basic : basicType -> message basicType
| key : keyType -> message basicType
| encrypt : message basicType -> keyType -> message basicType
| sign : message basicType -> keyType -> message basicType
| hash : message basicType -> message basicType
| pair : message basicType -> message basicType -> message basicType.

(** Predicate that determines if a message cannot be decrypted.  Could be
  that it is not encrypted to begin with or the wrong key is used. *)

Definition is_not_decryptable{T:Type}(m:message T)(k:keyType):Prop :=
  match m with
  | basic _ => True
  | key _ => True
  | encrypt m' k' => k <> inverse k'
  | sign _ _ => True
  | hash _ => True
  | pair _ _ => True
  end.

(** [decrypt] returns either a decrypted message or a proof of why the message
  cannot be decrypted. *)

Fixpoint decrypt{T:Type}(m:message T)(k:keyType):(message T)+{(is_not_decryptable m k)}.
refine
  match m with
  | basic c => inright _ _
  | key _ => inright _ _
  | encrypt m' j => (if (is_inverse k j) then (inleft _ m') else (inright _ _ ))
  | sign m' k => inright _ _
  | hash _ => inright _ _
  | pair _ _ => inright _ _
  end.
Proof.
  reflexivity.
  reflexivity.
  simpl. assumption.
  reflexivity.
  reflexivity.
  reflexivity.
Defined.
  
Eval compute in decrypt(encrypt nat (basic nat 1) (symmetric 1)) (symmetric 1).

Eval compute in decrypt(encrypt nat (basic nat 1) (symmetric 1)) (symmetric 2).

(** Predicate that determines if a message is properly signed. *)

Definition is_signed{T:Type}(m:message T)(k:keyType):Prop :=
  match m with
  | basic _ => False
  | key _ => False
  | encrypt _ _ => False
  | sign m' k' => k = inverse k'
  | hash _ => False
  | pair _ _ => False
  end.

(** Signature check returns either a proof that the signature is correct
  or a proof that the signature is not correct. *)

Fixpoint check{T:Type}(m:message T)(k:keyType):{(is_signed m k)}+{not (is_signed m k)}.
refine
  match m with
  | basic c => right _ _
  | key _ => right _ _
  | sign m' j => (if (is_inverse k j) then (left _ _) else (right _ _ ))
  | encrypt m' k => right _ _
  | hash _ => right _ _
  | pair _ _ => right _ _
  end.
Proof.
  unfold not. intros. simpl in H. assumption.
  unfold not. intros. simpl in H. assumption.
  unfold not. intros. simpl in H. assumption.
  destruct (is_inverse j k).
  simpl. rewrite _H. reflexivity.
  simpl. rewrite <- _H. reflexivity.
  simpl. assumption.
  unfold not. intros. simpl in H. assumption.
  unfold not. intros. simpl in H. assumption.
Defined.

Eval compute in check(sign nat (basic nat 1) (private 1)) (public 1).

Eval compute in check(sign nat (basic nat 1) (private 1)) (public 2).

Theorem check_dec: forall T, forall m:(message T), forall k, {(is_signed m k)}+{not (is_signed m k)}.
Proof.
  intros.
  destruct m.
  right. unfold is_signed. tauto.
  right. unfold is_signed. tauto.
  right. unfold is_signed. tauto.
  destruct (is_inverse k0 k).
  left. simpl. rewrite e. auto.
  right. unfold not. simpl. unfold not in n. intros. subst. auto.
  right. unfold is_signed. tauto.
  right. unfold is_signed. tauto.
Defined.

Eval compute in check_dec nat (sign nat (basic nat 1) (private 1)) (public 1).

Eval compute in check_dec nat (sign nat (basic nat 1) (private 1)) (public 2).


Require Import List.
Definition Name := nat.

Definition KeyServer  := list (Name * {k : keyType | exists x, k = public x}) % type.


SearchAbout exist .
Lemma noteqpOne : forall x : nat, S x <> x.
Proof.  intros. induction x. congruence. unfold not.  intros. inversion H. contradiction.  Qed.


Fixpoint nameinServer (n : Name) (ks : KeyServer): bool :=
  match ks with 
   | nil => false
   | x :: xs => match x with 
                 (na,kk) => if beq_nat na n then true else nameinServer n xs
                end
  end. 
Inductive keyServerError (ks : KeyServer): Prop :=
 | notAPublicKey : {k  | forall x, k <> public x} -> keyServerError ks
 | alreadyEntryForName : { n : Name | (nameinServer n ks) = true} -> keyServerError ks. 

SearchAbout In.
    
Definition addKey (ks : KeyServer) (name : Name) (k : keyType) : KeyServer + {keyServerError ks}.
Proof. destruct k. case (symmetric k). intros. right. constructor. exists (symmetric k) . intros. unfold not. intros. inversion H.
right. constructor. exists (private k). intros. unfold not. intros. inversion H.
left. assert ((public k) = (public k)). reflexivity.  refine ((name, _) ::ks).
eauto. Defined. 

Definition ks0 : KeyServer := nil.
Eval compute in addKey ks0 1 (public 1).
Eval compute in addKey ks0 1 (private 1).
Eval compute in addKey ks0 1 (symmetric 1).

Fixpoint realRemove (ks : KeyServer) (name :Name) : KeyServer :=
  match ks with 
    | nil => nil
    | x :: xs => if beq_nat (fst x) name then realRemove xs name else x :: (realRemove xs name)
  end.

Fixpoint  removeKey (ks : KeyServer) (name : Name) : KeyServer + {nameinServer name ks = false}.
  case_eq (nameinServer name ks). intros. left. exact (realRemove ks name).
  intros. right. reflexivity. Defined.

Definition PubProof :={k : keyType | exists x, k = public x}.


Definition pub2 : {k : keyType | exists x, k = public x}. exists (public 2). exists 2. reflexivity. Defined.   
Definition pub3 : PubProof. exists (public 3). exists 3. reflexivity. Defined.  

Definition ks3 := (2,pub2) :: ((3,pub3) :: ks0).
Eval compute in removeKey ks3 1.
Eval compute in removeKey ks3 2.
Eval compute in removeKey ks3 3.
Eval compute in removeKey ks3 4.

Definition publicServerKey := public 0.

Inductive Maybe {T : Type} :=
 | Just : T -> Maybe
 | Nothing : Maybe.

Fixpoint findMaybe (name : Name) (ks : KeyServer) : Maybe :=
  match ks with 
   | nil => Nothing
   | x :: xs => if beq_nat (fst x) name then Just (snd x) else findMaybe name xs
  end.

Theorem nameinServerNotEmpty : forall name : Name, forall ks : KeyServer,
  nameinServer name ks = true -> ks <> nil. 
Proof. intros. unfold not. intros. unfold nameinServer in H. rewrite H0 in H. inversion H. Defined.
(*Theorem babyStep0 : forall name : Name, forall ks : KeyServer, forall x, 
    nameinServer name ks = nameinServer name (x :: ks) -> nameinServer name ks = true. 
Proof. intros. rewrite H.  unfold nameinServer. intros.   let. .  .  inversion H.  destruct beq_nat in H1. exact (fst x). exact (fst x).   rewrite H. simpl. intros. rewrite H.  auto .  case_eq (beq_nat na name).  simpl in H. 
*)
Theorem babyStep : forall name : Name, forall ks : KeyServer, forall x,
  nameinServer name (x :: ks)= true -> name = (fst x) \/ nameinServer name ks = true.
Proof. intros. induction (fst x). induction name as [|name']. left. reflexivity.    induction (x :: ks).  Abort. 
(*simpl in H.   left. simpl. destruct x. assert (beq_nat n name = true). 
case_eq (beq_nat n name).  trivial. intros.  apply H.   simpl. inversion H. unfold fst.  
auto.  cbv. 


 simpl in H0. (* unfold beq_nat in H0. trivial.*)
SearchAbout beq_nat. apply beq_nat_true in H0.  rewrite H0.  reflexivity. 

 

Theorem find : forall name : Name, forall ks : KeyServer,
               nameinServer name ks = true -> exists x, findMaybe name ks = Just x.
Proof. intros. induction ks. apply nameinServerNotEmpty in H. elim H. reflexivity. 
simpl in H. 
assert ((fst a) = name \/ nameinServer name ks = true).

inversion H. apply H in IHks.  


  unfold nameinServer in H. inversion H. apply nameinServerNotEmpty in H. unfold not in H. induction ks. elim H1. inversion H1. 
apply nameinServerNotEmpty in H1.  .  H1.   unfold nameinServer in H. destruct ks. inversion H. fold nameinServer in H. inversion H. 
exists (snd p). unfold findMaybe.   
  constructor .
inversion H. simpl in H.   simpl in H.    

*)
Fixpoint requestKey (name :Name) (ks : KeyServer) : keyType + { findMaybe name ks = Nothing}. 
Proof. case_eq (findMaybe name ks). intros. left.  exact (proj1_sig s). right. reflexivity. 

(*

 name ks = false}.
Proof. case_eq (nameinServer name ks). intros.   induction (requestKey name ks).  (findMaybe name ks). intros. left.  exact (proj1_sig t). right. simpl.  

Fixpoint requestKey (name :Name) (ks : KeyServer) : Maybe := findMaybe name ks.  

*)

Inductive MessagePair (T : Type) := 
  messagepair : Name -> message T -> MessagePair T.
 
Definition send {T : Type} (pk : keyType) (encryp : keyType) (m : message T) (toGuy : Name) : {mp : MessagePair T | mp = messagepair T toGuy (sign T (encrypt T m encryp) pk)}.
Proof.  exists ( messagepair T toGuy (sign T (encrypt T m encryp) pk)). reflexivity. Defined. 


 (sign T (encrypt T m encryp) pk)).


     