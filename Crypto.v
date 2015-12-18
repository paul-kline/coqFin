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
Definition privateServerKey := private 0. 

Inductive Maybe {T : Type} :=
 | Just : T -> Maybe
 | Nothing : Maybe.
(*
Theorem inImpliesIn : forall T : Type, 
                      forall t : T,
                      forall t2 : T,
                      forall ls : list T,
                      In t ls 
*)
SearchAbout In.
Fixpoint findOr (name : Name) (ks : KeyServer) : { x :PubProof | In (name,x) ks} + {forall kp : PubProof, ~In (name,kp) ks}. 
Proof. induction ks. right.  intros.  simpl. unfold not.  intros.  apply H. 
destruct a.  case_eq (beq_nat name n).  intros. left.  exists s.  SearchAbout beq_nat. symmetry in H. apply beq_nat_eq in H. rewrite H. SearchAbout In. apply in_eq.   
intros. SearchAbout In. destruct IHks. left. destruct s0.  exists x. simpl. right. apply i. (* destruct s0. apply s0.  simpl.   exists s. exact p. right. *)
intros. assert (forall pp, ~ (n,s) = (name, pp)). intros.  unfold not. intros. inversion H0. SearchAbout beq_nat. apply beq_nat_false in H.   symmetry in H2. contradiction.
SearchAbout In. unfold not. right. intros. simpl in H1.  destruct H1.  apply H0 in H1.  apply H1. apply n0 in H1.  apply H1. Defined. 


(*
Fixpoint findMaybe (name : Name) (ks : KeyServer) : Maybe (T := PubProof).
Proof.  intros. remember k as p.   trivial. remember k. ( k : PubProof).



 :=
  match ks with 
   | nil => Nothing
   | x :: xs => if beq_nat (fst x) name then Just (snd x) else findMaybe name xs
  end.

Theorem findMaybeNotEmpty : forall name : Name, forall ks : KeyServer,
 forall s,  findMaybe name ks = Just s -> ks <> nil. 
Proof. intros. induction ks. intros.  simpl in H. inversion H. unfold not. intros.  inversion H0. Qed.
Theorem nameinServerNotEmpty : forall name : Name, forall ks : KeyServer,
  nameinServer name ks = true -> ks <> nil. 
Proof. intros. unfold not. intros. unfold nameinServer in H. rewrite H0 in H. inversion H. Defined.

Theorem notInImpliesNothings : forall (name : Name), forall ks : KeyServer, forall kp, ~(In (name,kp) ks) -> findMaybe name ks = Nothing.
Proof. intros.  unfold not in H. simpl.  

Theorem  findImpliesIn : forall (name : Name), forall (ks : KeyServer), forall (s : PubProof),
(findMaybe name ks = Just s) ->   In (name, s) ks.
Proof.  intros. exists s.  case_eq (findMaybe name ks). intros.  induction findMaybe. 
*)


Fixpoint requestKey {T : Type} (name :Name) (ks : KeyServer) : { m : message T | 
                                                                 exists kp, m = sign T (key T (proj1_sig kp)) privateServerKey /\
                                                                 In (name,kp) ks } + {forall kp, ~ (In (name,kp) ks)}. 
Proof. case_eq (findOr name ks). intros. destruct s.  left.  exists (sign T (key T (proj1_sig x)) privateServerKey). exists x. split. reflexivity. apply i. intros.    right. apply n. Defined.  



Fixpoint findMaybe (name : Name) (ks : KeyServer) : Maybe :=
  match ks with 
   | nil => Nothing
   | x :: xs => if beq_nat (fst x) name then Just (snd x) else findMaybe name xs
  end.

Theorem nameinServerNotEmpty : forall name : Name, forall ks : KeyServer,
  nameinServer name ks = true -> ks <> nil. 
Proof. intros. unfold not. intros. unfold nameinServer in H. rewrite H0 in H. inversion H. Defined.



Fixpoint requestKey2 (name :Name) (ks : KeyServer) : keyType + { findMaybe name ks = Nothing}. 
Proof. case_eq (findMaybe name ks). intros. left.  exact (proj1_sig s). right. reflexivity. Defined.  

















(*

 name ks = false}.
Proof. case_eq (nameinServer name ks). intros.   induction (requestKey name ks).  (findMaybe name ks). intros. left.  exact (proj1_sig t). right. simpl.  

Fixpoint requestKey (name :Name) (ks : KeyServer) : Maybe := findMaybe name ks.  

*)

Inductive RealMessage (T : Type) := 
  realmessage : Name -> Name -> message T -> RealMessage T.
 
Definition send {T : Type} (pk : keyType) (encryp : keyType) (m : message T) (fromGuy : Name) (toGuy : Name) : {mp : RealMessage T | mp = realmessage T fromGuy toGuy (sign T (encrypt T m encryp) pk)}.
Proof.  exists ( realmessage T fromGuy toGuy (sign T (encrypt T m encryp) pk)). reflexivity. Defined. 
Definition getFrom {T : Type} (mp : RealMessage T): Name :=
  match mp with
   | realmessage f t m => f
  end. 
Definition getTo {T : Type} (mp : RealMessage T): Name :=
  match mp with
   | realmessage f t m => t
  end.

Definition getMessage {T : Type} (mp : RealMessage T): message T :=
  match mp with
   | realmessage f t m => m
  end. 
Inductive MyError : Prop :=
  myerror : MyError.
(*
Definition checkServerMessage {T :Type} {ks : KeyServer} {name : Name} (mp : { m : message T |   exists kp, m = sign T (key T (proj1_sig kp)) privateServerKey /\
                                                   In (name,kp) ks }) : keyType. case_eq mp. intros.  destruct x. inversion e.    exists kp. e. destruct e. 
Proof. intros. 
Definition requestKey2{T : Type} (name: Name) (ks : KeyServer) : keyType  + {forall kp, ~ (In (name,kp) ks)}.

Proof. case_eq (requestKey ( T:=T) name ks ). intros. left.  destruct s. exact kp. elim e. destruct e. left.    simpl e. destruct e.  simpl in s.  remember (proj2_sig s).   left. destruct s. exact k.  case_eq s.  intros.  destruct s.   
*)
Inductive badbadnotgood {T : Type} ( mp : RealMessage T) (ks : KeyServer) (key : keyType) : Prop :=
  | notsignedman : (exists k, requestKey2 (getFrom mp) ks = inleft k /\ ~ (is_signed (getMessage mp) (k))) -> badbadnotgood mp ks key
  | cantdecryptman : { m : message T | exists innerM : message T, forall k, forall mm, innerM <> encrypt T mm k /\ exists someK,                                  
                       m = sign T innerM someK} -> badbadnotgood mp ks key
  | myKeyFails : badbadnotgood mp ks key
  | keyLookupFail : badbadnotgood mp ks key.

Theorem inverses : forall k1 k2, inverse k1 = k2 -> inverse k2 = k1.
Proof. intros. destruct k1.  
  simpl in H. rewrite <- H.  simpl. reflexivity. 
  simpl in H. rewrite <- H.  simpl. reflexivity.  
  simpl in H.  rewrite <- H. simpl. reflexivity. Qed. 

Definition receiveMessage {T : Type} (ks : KeyServer) (mp : RealMessage T) (mypriv : keyType) : 
   {res : message T |  exists kpub, (requestKey2 (getFrom mp) ks) = inleft kpub /\  (exists k2, (getMessage mp) = sign T (encrypt T res k2) (inverse kpub) /\
                       decrypt (encrypt T res k2) mypriv= (inleft res) )
                        }
                  
  + { badbadnotgood mp ks mypriv }.
Proof. case_eq (requestKey2 (getFrom mp) ks).  (*at this point, successful look up of pub key *)
  intros.    
    case_eq (getMessage mp).
       intros. right.  constructor. exists k. split.  apply H.  rewrite H0. simpl. unfold not. intros.  apply H1. 
       intros. right. constructor. exists k. split. apply H.  rewrite H0. simpl. unfold not. intros. apply H1. 
       intros. right. constructor. exists k. split. apply H.  rewrite H0. simpl. unfold not. intros. apply H1.
       intros. rename m into hopefullyEncrypted.
       case_eq (is_inverse k0 k).
        intros.  
         (* this is the signed case *)
         case_eq (hopefullyEncrypted). (* for all except encrypt form, return the error. *)
           intros.  right.  apply cantdecryptman. exists  (getMessage mp). exists hopefullyEncrypted. intros. unfold not. rewrite H2. split.  intros.  inversion H3. exists k0. rewrite H0. rewrite H2. reflexivity. 
           intros.   right.  apply cantdecryptman. exists  (getMessage mp). exists hopefullyEncrypted. intros. unfold not. rewrite H2. split.  intros.  inversion H3. exists k0. rewrite H0. rewrite H2. reflexivity.
           (*encrypt case *) intros. case_eq (decrypt hopefullyEncrypted mypriv). 
                                        intros.  left. exists m. exists k. split. reflexivity. exists k1. split.    rewrite e.  reflexivity.
                                            assert (m0 = m).  rewrite H2 in H3.  simpl in H3. destruct (is_inverse mypriv k1).  inversion H3.  reflexivity.  inversion H3.  rewrite <- H2. rewrite H4 in H3. apply H3. 
                                                                      
                                        intros. right. apply myKeyFails. (* this needs more descriptive args, but I'm really tired of this. *) 
           intros.    right.  apply cantdecryptman. exists  (getMessage mp). exists hopefullyEncrypted. intros. unfold not. rewrite H2. split.  intros.  inversion H3. exists k0. rewrite H0. rewrite H2. reflexivity. 
           intros.    right.  apply cantdecryptman. exists  (getMessage mp). exists hopefullyEncrypted. intros. unfold not. rewrite H2. split.  intros.  inversion H3. exists k0. rewrite H0. rewrite H2. reflexivity. 
           intros.    right.  apply cantdecryptman. exists  (getMessage mp). exists hopefullyEncrypted. intros. unfold not. rewrite H2. split.  intros.  inversion H3. exists k0. rewrite H0. rewrite H2. reflexivity. 
           intros. right. constructor. exists k. split. apply H.  rewrite H0. simpl. unfold not. intros. unfold not in n.  symmetry in H2. apply inverses in H2. symmetry in H2.   apply n in H2. apply H2.
intros. right. constructor. exists k. split. apply H.  rewrite H0. simpl. unfold not. intros. apply H1.
intros. right. constructor. exists k. split. apply H.  rewrite H0. simpl. unfold not. intros. apply H1.
   intros. right.  apply keyLookupFail. (* needs more args again.*) Defined. 

Definition engage {T: Type} (a : Name) (aPriv : keyType) (b: Name) ( bPriv : keyType) (ks : KeyServer) (m : message T) := 
   match requestKey2 b ks with 
     | inright _ => false
     | inleft bPub => match receiveMessage ks (proj1_sig  (send bPriv aPriv m a b) ) bPriv with
                          | inright _ => false
                          | inleft _ => true
                      end
   end. 

(*
Theorem Any message leaving a sending node is encrypted and signedsendTheorem     -- this is proven in the return type of send. 
)*)






     