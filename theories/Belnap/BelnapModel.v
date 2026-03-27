Set Warnings "-stdlib-vector".
Set Warnings "-redundant-canonical-projection".
Set Warnings "-notation-overridden".
Set Warnings "-signature-auto-inline".

From Stdlib Require Import NArith Arith Lia Bool List Btauto.
From Stdlib Require Import Vectors.Vector Vectors.Fin.
From Stdlib Require Import Vectors.VectorSpec.
Import VectorNotations.

From Equations Require Import Equations.

From HB Require Import structures.

Derive Signature for Vector.t.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype choice order.
Import Order.Theory.

(* ============================= Storage layout ============================= *)

Definition bits_per_word : nat := 64.

Definition words_per_plane (n : nat) : nat :=
  (n + (bits_per_word - 1)) / bits_per_word.

(** [double n] computes [2 * n] via a fixpoint that reduces definitionally:
    [double (S n') ≡ S (S (double n'))].
    This lets Equations pattern-match vectors of length [double n] without
    explicit [eq_rect] casts. *)
Fixpoint double (n : nat) : nat :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Lemma double_eq_mul2 (n : nat) : double n = 2 * n.
Proof. induction n; simpl; lia. Qed.

Definition storage_size (n : nat) : nat :=
  double (words_per_plane n).

(* ============================= Belnap scalar type ============================= *)

Inductive Belnap : Type :=
| unknown : Belnap
| btrue   : Belnap
| bfalse  : Belnap
| both    : Belnap.

Scheme Equality for Belnap.

(* ============================= Fin.t convenience ============================= *)

Notation fin_val i := (proj1_sig (Fin.to_nat i)).
Notation fin_lt  i := (proj2_sig (Fin.to_nat i)).

(* ============================= Encoding / decoding ============================= *)

(** [encode_belnap b bit] returns (pos_contribution, neg_contribution) already
    shifted to bit position [bit], suitable for OR-ing into the word pair. *)
Definition encode_belnap (b : Belnap) (bit : nat) : N * N :=
  let shifted := N.shiftl 1%N (N.of_nat bit) in
  match b with
  | unknown => (0%N, 0%N)
  | btrue   => (shifted, 0%N)
  | bfalse  => (0%N, shifted)
  | both    => (shifted, shifted)
  end.

(** [decode_belnap posBit negBit] decodes from two extracted single bits (0 or 1). *)
Definition decode_belnap (posBit negBit : N) : Belnap :=
  match N.eqb posBit 0%N, N.eqb negBit 0%N with
  | true,  true  => unknown
  | false, true  => btrue
  | true,  false => bfalse
  | false, false => both
  end.

(* ============================= Arithmetic lemmas ============================= *)

Lemma word_pair_in_bounds (n i : nat) (h : i < n) :
  2 * (i / bits_per_word) + 1 < storage_size n.
Proof.
  unfold storage_size. rewrite double_eq_mul2.
  unfold words_per_plane, bits_per_word.
  simpl (64 - 1).
  assert (H1 : i + 64 <= n + 63) by lia.
  assert (H2 : (i + 64) / 64 <= (n + 63) / 64).
  { apply Nat.Div0.div_le_mono; exact H1. }
  assert (H3 : (i + 64) / 64 = i / 64 + 1).
  { replace (i + 64) with (i + 1 * 64) by lia. apply Nat.div_add. lia. }
  lia.
Qed.

Lemma even_word_in_bounds (n i : nat) (h : i < n) :
  2 * (i / bits_per_word) < storage_size n.
Proof. pose proof (word_pair_in_bounds n i h). lia. Qed.

(* ============================= Raw storage vectors ============================= *)

Local Notation BVec n := (Vector.t N (storage_size n)).

(* ============================= Element access helpers ============================= *)

Definition word_index {n : nat} (i : Fin.t n) : nat :=
  fin_val i / bits_per_word.

Definition bit_index {n : nat} (i : Fin.t n) : nat :=
  fin_val i mod bits_per_word.

Definition pos_word_fin {n : nat} (i : Fin.t n) : Fin.t (storage_size n) :=
  Fin.of_nat_lt (even_word_in_bounds n (fin_val i) (fin_lt i)).

Definition neg_word_fin {n : nat} (i : Fin.t n) : Fin.t (storage_size n) :=
  Fin.of_nat_lt (word_pair_in_bounds n (fin_val i) (fin_lt i)).

(* ============================= bv_get ============================= *)

Definition bv_get {n : nat} (i : Fin.t n) (bv : BVec n) : Belnap :=
  let b := bit_index i in
  let posW := Vector.nth bv (pos_word_fin i) in
  let negW := Vector.nth bv (neg_word_fin i) in
  let posBit := N.land (N.shiftr posW (N.of_nat b)) 1%N in
  let negBit := N.land (N.shiftr negW (N.of_nat b)) 1%N in
  decode_belnap posBit negBit.

(* ============================= bv_set ============================= *)

(** NOTE: N.lnot x 64%N computes the 64-bit bitwise complement of x.
    The explicit width argument 64%N must always be used here; the extraction
    directive in BelnapExtract.v drops this argument for Int64.lognot. *)
Definition bv_set {n : nat} (i : Fin.t n) (b : Belnap) (bv : BVec n) : BVec n :=
  let bit := bit_index i in
  let bitMask := N.lnot (N.shiftl 1%N (N.of_nat bit)) 64%N in
  let '(posBit, negBit) := encode_belnap b bit in
  let bv' := Vector.replace bv (pos_word_fin i)
               (N.lor (N.land (Vector.nth bv (pos_word_fin i)) bitMask) posBit) in
  Vector.replace bv' (neg_word_fin i) (N.lor (N.land (Vector.nth bv' (neg_word_fin i)) bitMask) negBit).

(* ============================= tail_mask + mask_tail ============================= *)

Definition tail_mask (n : nat) : N :=
  let rem := n mod bits_per_word in
  if rem =? 0 then N.ones 64 else N.ones (N.of_nat rem).

Program Definition mask_tail {n : nat} (bv : BVec n) : BVec n :=
  match words_per_plane n as nw return nw = words_per_plane n -> BVec n with
  | 0 => fun _ => bv
  | S nw' => fun Hnw =>
               let m := tail_mask n in
               if N.eqb m (N.ones 64) then bv
               else
                 let base := 2 * nw' in
                 let hb  : Fin.t (storage_size n) := @Fin.of_nat_lt base (storage_size n) _ in
                 let hb1 : Fin.t (storage_size n) := @Fin.of_nat_lt (base + 1) (storage_size n) _ in
                 let bv' := Vector.replace bv hb  (N.land (Vector.nth bv hb) m) in
                 Vector.replace bv' hb1 (N.land (Vector.nth bv' hb1) m)
  end Logic.eq_refl.

Next Obligation. unfold storage_size. rewrite double_eq_mul2. rewrite <- Hnw. lia. Qed.

Next Obligation. unfold storage_size. rewrite double_eq_mul2. rewrite <- Hnw. lia. Qed.

(* ============================= deinterleave / interleave ============================= *)

(** Split a vector of length [double n] into its even- and odd-indexed elements.
    Because [double (S n') ≡ S (S (double n'))], Equations can directly pattern-match
    the first two elements without any [eq_rect] cast. *)
Equations deinterleave {A : Type} (n : nat) (v : Vector.t A (double n)) : Vector.t A n * Vector.t A n :=
  deinterleave 0 _ := ([], []);
  deinterleave (S n') (e :: o :: rest) :=
    let '(evens, odds) := deinterleave n' rest in
    (e :: evens, o :: odds).

(** Interleave two vectors of the same length into a single vector of [double] length. *)
Equations interleave {A : Type} (n : nat) (evens odds : Vector.t A n) : Vector.t A (double n) :=
  interleave 0 [] [] := [];
  interleave (S n') (e :: es) (o :: os) := e :: o :: interleave n' es os.

(** Round-trip: deinterleave . interleave = id *)
Lemma deinterleave_interleave {A : Type} (n : nat) (e o : Vector.t A n) :
  deinterleave n (interleave n e o) = (e, o).
Proof.
  funelim (interleave n e o); simp interleave deinterleave; rewrite ?H; reflexivity.
Qed.

(** Round-trip: interleave . deinterleave = id *)
Lemma interleave_deinterleave {A : Type} (n : nat) (v : Vector.t A (double n)) :
  let '(e, o) := deinterleave n v in interleave n e o = v.
Proof.
  funelim (deinterleave n v).
  - depelim v. simp deinterleave interleave. reflexivity.
  - destruct (deinterleave _ rest) as [evens odds].
    simp interleave. rewrite H. reflexivity.
Qed.

(** Deinterleaving a constant vector yields two copies. *)
Lemma deinterleave_const {A : Type} (n : nat) (c : A) :
  deinterleave n (Vector.const c (double n)) = (Vector.const c n, Vector.const c n).
Proof.
  induction n as [|n' IH].
  - simp deinterleave. reflexivity.
  - change (Vector.const c (double (S n')))
      with (Vector.cons A c _ (Vector.cons A c _ (Vector.const c (double n')))).
    simp deinterleave. rewrite IH. reflexivity.
Qed.

Lemma interleave_const {A : Type} (n : nat) (c : A) :
  interleave n (Vector.const c n) (Vector.const c n) = Vector.const c (double n).
Proof.
  pose proof (interleave_deinterleave n (Vector.const c (double n))) as H.
  rewrite deinterleave_const in H. exact H.
Qed.

(* ============================= Vector helpers ============================= *)

Lemma vec_map2_nth {A B C n} (f : A -> B -> C)
  (a : Vector.t A n) (b : Vector.t B n) (i : Fin.t n) :
  Vector.nth (Vector.map2 f a b) i = f (Vector.nth a i) (Vector.nth b i).
Proof.
  induction n as [| n' IH].
  - inversion i.
  - rewrite (Vector.eta a). rewrite (Vector.eta b).
    apply (Fin.caseS' i).
    + reflexivity.
    + intros j. simpl. apply IH.
Qed.

(* ============================= Bulk operations ============================= *)

(** Apply [posOp] to the pos-plane words and [negOp] to the neg-plane words. *)
Definition vec_binop_storage (posOp negOp : N -> N -> N) {n : nat} (a b : BVec n) : BVec n :=
  let wp := words_per_plane n in
  let '(aP, aN) := deinterleave wp a in
  let '(bP, bN) := deinterleave wp b in
  interleave wp (Vector.map2 posOp aP bP) (Vector.map2 negOp aN bN).

Definition vec_not {n : nat} (bv : BVec n) : BVec n :=
  let wp := words_per_plane n in
  let '(pos, neg) := deinterleave wp bv in
  interleave wp neg pos.

Definition vec_and       {n} (a b : BVec n) := vec_binop_storage N.land N.land a b.
Definition vec_or        {n} (a b : BVec n) := vec_binop_storage N.lor  N.lor  a b.
Definition vec_consensus {n} (a b : BVec n) := vec_binop_storage N.land N.lor  a b.
Definition vec_merge     {n} (a b : BVec n) := vec_binop_storage N.lor  N.land a b.

(* ============================= Initialization ============================= *)

Definition all_unknown (n : nat) : BVec n :=
  Vector.const 0%N (storage_size n).

Definition all_both (n : nat) : BVec n :=
  Vector.const (N.ones 64) (storage_size n).

Definition all_true (n : nat) : BVec n :=
  let wp := words_per_plane n in
  interleave wp (Vector.const (N.ones 64) wp) (Vector.const 0%N wp).

Definition all_false (n : nat) : BVec n :=
  let wp := words_per_plane n in
  interleave wp (Vector.const 0%N wp) (Vector.const (N.ones 64) wp).

(* ============================= 64-bit word boundedness ============================= *)

Definition word_bounded (w : N) : bool := (w <=? N.ones 64)%N.

Fixpoint vec_all {A : Type} {m : nat} (p : A -> bool) (v : Vector.t A m) : bool :=
  match v with
  | [] => true
  | h :: t => p h && vec_all p t
  end.

Definition bv_bounded {n : nat} (bv : BVec n) : bool :=
  vec_all word_bounded bv.

Lemma word_bounded_0 : word_bounded 0 = true.
Proof. reflexivity. Qed.

Lemma word_bounded_ones64 : word_bounded (N.ones 64) = true.
Proof. unfold word_bounded. apply N.leb_refl. Qed.

Lemma word_bounded_log2 (w : N) :
  word_bounded w = true -> (w = 0%N \/ (N.log2 w < 64)%N).
Proof.
  unfold word_bounded. intro H. apply N.leb_le in H.
  destruct (N.eq_dec w 0%N) as [->|Hw]; [left; reflexivity | right].
  apply N.log2_le_mono in H.
  rewrite N.ones_equiv in H.
  have H64 : (N.log2 (N.pred (2 ^ 64)) = 63)%N by reflexivity.
  rewrite H64 in H. lia.
Qed.

Lemma word_bounded_land_ones (w : N) :
  word_bounded w = true -> N.land w (N.ones 64) = w.
Proof.
  intro H. apply word_bounded_log2 in H. destruct H as [-> | H].
  - apply N.bits_inj. intro k. rewrite N.land_spec. rewrite N.bits_0. reflexivity.
  - apply N.land_ones_low. exact H.
Qed.

Lemma word_bounded_lor_ones (w : N) :
  word_bounded w = true -> N.lor (N.ones 64) w = N.ones 64.
Proof.
  intro H. rewrite N.lor_comm. apply word_bounded_log2 in H. destruct H as [-> | H].
  - rewrite N.lor_0_l. reflexivity.
  - apply N.lor_ones_low. exact H.
Qed.

Lemma word_bounded_land (a b : N) :
  word_bounded a = true -> word_bounded (N.land a b) = true.
Proof.
  unfold word_bounded. intro Ha. apply N.leb_le. apply N.leb_le in Ha.
  etransitivity; [apply N.land_le_l | exact Ha].
Qed.

Lemma word_bounded_lor (a b : N) :
  word_bounded a = true -> word_bounded b = true -> word_bounded (N.lor a b) = true.
Proof.
  intros Ha Hb.
  destruct (N.eq_dec a 0) as [->|Ha0]; [rewrite N.lor_0_l; exact Hb|].
  destruct (N.eq_dec b 0) as [->|Hb0]; [rewrite N.lor_0_r; exact Ha|].
  destruct (N.eq_dec (N.lor a b) 0) as [->|Hab0]; [reflexivity|].
  unfold word_bounded. apply N.leb_le. rewrite N.ones_equiv.
  apply N.lt_le_pred. apply N.log2_lt_pow2; [lia|].
  rewrite N.log2_lor.
  apply word_bounded_log2 in Ha as [->|Ha]; [contradiction|].
  apply word_bounded_log2 in Hb as [->|Hb]; [contradiction|].
  apply N.max_lub_lt; assumption.
Qed.

Lemma vec_all_const {A : Type} {m : nat} (p : A -> bool) (c : A) :
  p c = true -> vec_all p (Vector.const c m) = true.
Proof.
  intro Hc. induction m as [|m' IH]; simpl.
  - reflexivity.
  - rewrite Hc. exact IH.
Qed.

Lemma vec_all_nth {A : Type} {m : nat} (p : A -> bool) (v : Vector.t A m) :
  vec_all p v = true <-> forall i : Fin.t m, p (Vector.nth v i) = true.
Proof.
  induction v as [|h m' t IH].
  - split; [intros _ i; inversion i | reflexivity].
  - simpl. split.
    + intro H. apply andb_prop in H. destruct H as [Hh Ht].
      intro i. apply (Fin.caseS' i).
      * exact Hh.
      * intro j. apply IH. exact Ht.
    + intro H.
      have Hh : p h = true := H Fin.F1.
      rewrite Hh. simpl. apply IH. intro j. exact (H (Fin.FS j)).
Qed.

Lemma vec_all_map2 {A : Type} {m : nat} (p : A -> bool) (f : A -> A -> A)
  (Hf : forall x y, p x = true -> p y = true -> p (f x y) = true)
  {a b : Vector.t A m} :
  vec_all p a = true -> vec_all p b = true -> vec_all p (Vector.map2 f a b) = true.
Proof.
  intros Ha Hb. apply vec_all_nth. intro i.
  rewrite vec_map2_nth.
  apply Hf; [apply (vec_all_nth p a) | apply (vec_all_nth p b)]; assumption.
Qed.

Lemma vec_all_interleave {A : Type} (n : nat) (p : A -> bool) (e o : Vector.t A n) :
  vec_all p e = true -> vec_all p o = true -> vec_all p (interleave n e o) = true.
Proof.
  funelim (interleave n e o); simp interleave; simpl.
  - reflexivity.
  - intros He Ho. simpl in He, Ho.
    apply andb_prop in He. destruct He as [He1 He2].
    apply andb_prop in Ho. destruct Ho as [Ho1 Ho2].
    rewrite He1. simpl. rewrite Ho1. simpl.
    apply H; assumption.
Qed.

Lemma vec_all_deinterleave {A : Type} (n : nat) (p : A -> bool) (v : Vector.t A (double n)) :
  vec_all p v = true ->
  vec_all p (fst (deinterleave n v)) = true /\ vec_all p (snd (deinterleave n v)) = true.
Proof.
  funelim (deinterleave n v); simp deinterleave; intro Hv.
  - split; reflexivity.
  - simpl in Hv.
    apply andb_prop in Hv as [He Hv].
    apply andb_prop in Hv as [Ho Hv].
    specialize (H p Hv).
    destruct (deinterleave _ rest) as [evens odds]. simpl in *.
    destruct H as [IHe IHo].
    split. { simpl. rewrite He. simpl. assumption. }
    { simpl. rewrite Ho. simpl. assumption. }
Qed.

(* --- bv_bounded for constants --- *)

Lemma bv_bounded_all_unknown (n : nat) : bv_bounded (all_unknown n) = true.
Proof. unfold bv_bounded, all_unknown. apply vec_all_const. exact word_bounded_0. Qed.

Lemma bv_bounded_all_both (n : nat) : bv_bounded (all_both n) = true.
Proof. unfold bv_bounded, all_both. apply vec_all_const. exact word_bounded_ones64. Qed.

Lemma bv_bounded_all_true (n : nat) : bv_bounded (all_true n) = true.
Proof.
  unfold bv_bounded, all_true.
  apply vec_all_interleave; apply vec_all_const;
    [exact word_bounded_ones64 | exact word_bounded_0].
Qed.

Lemma bv_bounded_all_false (n : nat) : bv_bounded (all_false n) = true.
Proof.
  unfold bv_bounded, all_false.
  apply vec_all_interleave; apply vec_all_const;
    [exact word_bounded_0 | exact word_bounded_ones64].
Qed.

(* --- bv_bounded preservation for operations --- *)

Lemma bv_bounded_vec_binop_storage (fP fN : N -> N -> N)
  (HfP : forall x y, word_bounded x = true -> word_bounded y = true ->
                     word_bounded (fP x y) = true)
  (HfN : forall x y, word_bounded x = true -> word_bounded y = true ->
                     word_bounded (fN x y) = true)
  {n : nat} (a b : BVec n) :
  bv_bounded a = true -> bv_bounded b = true ->
  bv_bounded (vec_binop_storage fP fN a b) = true.
Proof.
  intros Ha Hb. unfold bv_bounded, vec_binop_storage.
  set (wp := words_per_plane n).
  pose proof (vec_all_deinterleave wp word_bounded a Ha) as [HaP HaN].
  pose proof (vec_all_deinterleave wp word_bounded b Hb) as [HbP HbN].
  destruct (deinterleave wp a) as [aP aN]. simpl in *.
  destruct (deinterleave wp b) as [bP bN]. simpl in *.
  apply vec_all_interleave.
  - exact (vec_all_map2 _ _ HfP HaP HbP).
  - exact (vec_all_map2 _ _ HfN HaN HbN).
Qed.

Lemma bv_bounded_vec_and {n} (a b : BVec n) :
  bv_bounded a = true -> bv_bounded b = true ->
  bv_bounded (vec_and a b) = true.
Proof.
  apply bv_bounded_vec_binop_storage.
  - intros x y Hx _. exact (word_bounded_land x y Hx).
  - intros x y Hx _. exact (word_bounded_land x y Hx).
Qed.

Lemma bv_bounded_vec_or {n} (a b : BVec n) :
  bv_bounded a = true -> bv_bounded b = true ->
  bv_bounded (vec_or a b) = true.
Proof. apply bv_bounded_vec_binop_storage; exact word_bounded_lor. Qed.

Lemma bv_bounded_vec_consensus {n} (a b : BVec n) :
  bv_bounded a = true -> bv_bounded b = true ->
  bv_bounded (vec_consensus a b) = true.
Proof.
  apply bv_bounded_vec_binop_storage.
  - intros x y Hx _. exact (word_bounded_land x y Hx).
  - exact word_bounded_lor.
Qed.

Lemma bv_bounded_vec_merge {n} (a b : BVec n) :
  bv_bounded a = true -> bv_bounded b = true ->
  bv_bounded (vec_merge a b) = true.
Proof.
  apply bv_bounded_vec_binop_storage.
  - exact word_bounded_lor.
  - intros x y Hx _. exact (word_bounded_land x y Hx).
Qed.

(* --- Vector-level bottom/top lemmas --- *)

Lemma vec_map2_land_const0_l {m} (v : Vector.t N m) :
  Vector.map2 N.land (Vector.const 0%N m) v = Vector.const 0%N m.
Proof.
  apply Vector.eq_nth_iff. intros p q <-.
  rewrite vec_map2_nth. rewrite Vector.const_nth. apply N.land_0_l.
Qed.

Lemma vec_map2_land_ones_r {m} (v : Vector.t N m) :
  vec_all word_bounded v = true ->
  Vector.map2 N.land v (Vector.const (N.ones 64) m) = v.
Proof.
  intro H. apply Vector.eq_nth_iff. intros p q <-.
  rewrite vec_map2_nth. rewrite Vector.const_nth.
  apply word_bounded_land_ones. apply (vec_all_nth word_bounded v). exact H.
Qed.

Lemma vec_map2_lor_ones_l {m} (v : Vector.t N m) :
  vec_all word_bounded v = true ->
  Vector.map2 N.lor (Vector.const (N.ones 64) m) v = Vector.const (N.ones 64) m.
Proof.
  intro H. apply Vector.eq_nth_iff. intros p q <-.
  rewrite vec_map2_nth. rewrite !Vector.const_nth.
  apply word_bounded_lor_ones. apply (vec_all_nth word_bounded v). exact H.
Qed.

Lemma vec_map2_lor_const0_r {m} (v : Vector.t N m) :
  Vector.map2 N.lor v (Vector.const 0%N m) = v.
Proof.
  apply Vector.eq_nth_iff. intros p q <-.
  rewrite vec_map2_nth. rewrite Vector.const_nth. apply N.lor_0_r.
Qed.

Lemma vec_and_all_unknown_l {n} (x : BVec n) :
  vec_and (all_unknown n) x = all_unknown n.
Proof.
  unfold vec_and, vec_binop_storage, all_unknown, storage_size.
  set (wp := words_per_plane n).
  rewrite deinterleave_const.
  destruct (deinterleave wp x) as [xP xN].
  rewrite !vec_map2_land_const0_l.
  exact (interleave_const wp 0%N).
Qed.

Lemma vec_and_all_both_r {n} (x : BVec n) :
  bv_bounded x = true -> vec_and x (all_both n) = x.
Proof.
  intro Hx. unfold vec_and, vec_binop_storage, all_both.
  set (wp := words_per_plane n).
  rewrite deinterleave_const.
  unfold bv_bounded in Hx.
  pose proof (vec_all_deinterleave wp word_bounded x Hx) as [HxP HxN].
  destruct (deinterleave wp x) as [xP xN] eqn:Hdx. simpl in *.
  rewrite (vec_map2_land_ones_r xP HxP).
  rewrite (vec_map2_land_ones_r xN HxN).
  pose proof (interleave_deinterleave wp x) as Hrt.
  rewrite Hdx in Hrt. exact Hrt.
Qed.

Lemma vec_consensus_all_false_l {n} (x : BVec n) :
  bv_bounded x = true -> vec_consensus (all_false n) x = all_false n.
Proof.
  intro Hx. unfold vec_consensus, vec_binop_storage, all_false.
  set (wp := words_per_plane n).
  rewrite deinterleave_interleave.
  unfold bv_bounded in Hx.
  pose proof (vec_all_deinterleave wp word_bounded x Hx) as [HxP HxN].
  destruct (deinterleave wp x) as [xP xN]. simpl in *.
  rewrite vec_map2_land_const0_l.
  rewrite (vec_map2_lor_ones_l xN HxN).
  reflexivity.
Qed.

Lemma vec_consensus_all_true_r {n} (x : BVec n) :
  bv_bounded x = true -> vec_consensus x (all_true n) = x.
Proof.
  intro Hx. unfold vec_consensus, vec_binop_storage, all_true.
  set (wp := words_per_plane n).
  rewrite deinterleave_interleave.
  unfold bv_bounded in Hx.
  pose proof (vec_all_deinterleave wp word_bounded x Hx) as [HxP HxN].
  destruct (deinterleave wp x) as [xP xN] eqn:Hdx. simpl in *.
  rewrite (vec_map2_land_ones_r xP HxP).
  rewrite vec_map2_lor_const0_r.
  pose proof (interleave_deinterleave wp x) as Hrt.
  rewrite Hdx in Hrt. exact Hrt.
Qed.

(* ============================= Sanity checks ============================= *)

Example get_all_unknown_is_unknown :
  bv_get Fin.F1 (all_unknown 64) = unknown.
Proof. reflexivity. Qed.

Example roundtrip_btrue :
  bv_get Fin.F1 (bv_set Fin.F1 btrue (all_unknown 64)) = btrue.
Proof. reflexivity. Qed.

(* ============================= Word-level bitwise lemmas ============================= *)

Lemma N_land_lor_diag (x y : N) : N.land x (N.lor x y) = x.
Proof. apply N.bits_inj. intro k. rewrite N.land_spec; rewrite N.lor_spec. btauto. Qed.

Lemma N_lor_land_diag (x y : N) : N.lor x (N.land x y) = x.
Proof. apply N.bits_inj. intro k. rewrite N.lor_spec; rewrite N.land_spec. btauto. Qed.

(* ============================= Vector map2 helpers ============================= *)

Lemma vec_map2_comm {A n} (f : A -> A -> A)
  (comm : forall x y, f x y = f y x) (a b : Vector.t A n) :
  Vector.map2 f a b = Vector.map2 f b a.
Proof.
  apply Vector.eq_nth_iff. intros p q <-.
  rewrite !vec_map2_nth. apply comm.
Qed.

Lemma vec_map2_assoc {A n} (f : A -> A -> A)
  (assoc : forall x y z, f x (f y z) = f (f x y) z)
  (a b c : Vector.t A n) :
  Vector.map2 f a (Vector.map2 f b c) = Vector.map2 f (Vector.map2 f a b) c.
Proof.
  apply Vector.eq_nth_iff. intros p q <-.
  rewrite !vec_map2_nth. apply assoc.
Qed.

Lemma vec_map2_absorb {A n} (f g : A -> A -> A)
  (abs : forall a b, f a (g a b) = a) (a b : Vector.t A n) :
  Vector.map2 f a (Vector.map2 g a b) = a.
Proof.
  apply Vector.eq_nth_iff. intros p q <-.
  rewrite !vec_map2_nth. apply abs.
Qed.

(* ============================= vec_binop_storage structural lemmas ============================= *)

Lemma vec_binop_storage_deinterleave {n} posOp negOp (a b : BVec n) :
  deinterleave (words_per_plane n) (vec_binop_storage posOp negOp a b) =
    let '(aP, aN) := deinterleave (words_per_plane n) a in
    let '(bP, bN) := deinterleave (words_per_plane n) b in
    (Vector.map2 posOp aP bP, Vector.map2 negOp aN bN).
Proof.
  unfold vec_binop_storage.
  set (wp := words_per_plane n).
  destruct (deinterleave wp a) as [aP aN].
  destruct (deinterleave wp b) as [bP bN].
  apply deinterleave_interleave.
Qed.

Lemma vec_binop_storage_comm {n} (fP fN : N -> N -> N)
  (commP : forall x y, fP x y = fP y x)
  (commN : forall x y, fN x y = fN y x)
  (a b : BVec n) :
  vec_binop_storage fP fN a b = vec_binop_storage fP fN b a.
Proof.
  unfold vec_binop_storage.
  destruct (deinterleave (words_per_plane n) a) as [aP aN].
  destruct (deinterleave (words_per_plane n) b) as [bP bN].
  f_equal; [apply vec_map2_comm; exact commP | apply vec_map2_comm; exact commN].
Qed.

Lemma vec_binop_storage_assoc {n} (fP fN : N -> N -> N)
  (assocP : forall x y z, fP x (fP y z) = fP (fP x y) z)
  (assocN : forall x y z, fN x (fN y z) = fN (fN x y) z)
  (a b c : BVec n) :
  vec_binop_storage fP fN a (vec_binop_storage fP fN b c) =
    vec_binop_storage fP fN (vec_binop_storage fP fN a b) c.
Proof.
  unfold vec_binop_storage.
  set (wp := words_per_plane n).
  destruct (deinterleave wp a) as [aP aN] eqn:Ha.
  destruct (deinterleave wp b) as [bP bN] eqn:Hb.
  destruct (deinterleave wp c) as [cP cN] eqn:Hc.
  rewrite (deinterleave_interleave wp (Vector.map2 fP bP cP) (Vector.map2 fN bN cN)).
  rewrite (deinterleave_interleave wp (Vector.map2 fP aP bP) (Vector.map2 fN aN bN)).
  f_equal; [apply vec_map2_assoc; exact assocP | apply vec_map2_assoc; exact assocN].
Qed.

Lemma vec_binop_storage_absorb {n} (fP1 fN1 fP2 fN2 : N -> N -> N)
  (HabsP : forall a b, fP1 a (fP2 a b) = a)
  (HabsN : forall a b, fN1 a (fN2 a b) = a)
  (a b : BVec n) :
  vec_binop_storage fP1 fN1 a (vec_binop_storage fP2 fN2 a b) = a.
Proof.
  unfold vec_binop_storage.
  set (wp := words_per_plane n).
  destruct (deinterleave wp a) as [aP aN] eqn:Ha.
  destruct (deinterleave wp b) as [bP bN].
  rewrite (deinterleave_interleave wp _ _).
  rewrite (vec_map2_absorb _ _ HabsP). rewrite (vec_map2_absorb _ _ HabsN).
  pose proof (interleave_deinterleave wp a) as Hrt.
  rewrite Ha in Hrt. exact Hrt.
Qed.

(* ============================= Idempotence ============================= *)

Lemma vec_map2_idem {A n} (f : A -> A -> A)
  (idem : forall x, f x x = x) (v : Vector.t A n) :
  Vector.map2 f v v = v.
Proof.
  apply Vector.eq_nth_iff. intros p q <-.
  rewrite vec_map2_nth. apply idem.
Qed.

Lemma vec_binop_storage_idem (fP fN : N -> N -> N)
  (HfP : forall x, fP x x = x) (HfN : forall x, fN x x = x)
  {n} (v : BVec n) : vec_binop_storage fP fN v v = v.
Proof.
  unfold vec_binop_storage.
  set (wp := words_per_plane n).
  destruct (deinterleave wp v) as [P Q] eqn:Hv.
  rewrite (vec_map2_idem _ HfP). rewrite (vec_map2_idem _ HfN).
  pose proof (interleave_deinterleave wp v) as Hrt.
  rewrite Hv in Hrt. exact Hrt.
Qed.

(* ============================= countType instance for N ============================= *)

Lemma N_pickleK : pcancel N.to_nat (fun n => Some (N.of_nat n)).
Proof. intro x. f_equal. exact (N2Nat.id x). Qed.

HB.instance Definition N_isCountable := isCountable.Build N N_pickleK.

(* ============================= list_to_vec helper for pcancel ============================= *)

Fixpoint list_to_vec {A : Type} (default : A) (n : nat) (l : list A) : Vector.t A n :=
  match n with
  | 0    => []
  | S n' => match l with
            | List.nil      => Vector.const default (S n')
            | List.cons h t => Vector.cons A h n' (list_to_vec default n' t)
            end
  end.

Lemma list_to_vec_to_list {A n} (default : A) (v : Vector.t A n) :
  list_to_vec default n (Vector.to_list v) = v.
Proof.
  induction v as [| h n' t IH].
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

Lemma to_list_length_gen {A n} (v : Vector.t A n) :
  length (Vector.to_list v) = n.
Proof.
  induction v; simpl; [reflexivity | f_equal; exact IHv].
Qed.

(* ============================= countType instance for BVec n ============================= *)

Definition bv_from_list (n : nat) (l : list N) : option (BVec n) :=
  if Nat.eqb (length l) (storage_size n)
  then Some (list_to_vec 0%N (storage_size n) l)
  else None.

Lemma bv_pcancel (n : nat) (bv : BVec n) :
  bv_from_list n (Vector.to_list bv) = Some bv.
Proof.
  unfold bv_from_list.
  rewrite to_list_length_gen.
  rewrite Nat.eqb_refl.
  rewrite (list_to_vec_to_list 0%N bv). reflexivity.
Qed.

(** Build countType for BVec n via pcancel through list N. *)
Definition bv_pickle {n : nat} (bv : BVec n) : nat :=
  pickle (Vector.to_list bv).

Definition bv_unpickle (n : nat) (k : nat) : option (BVec n) :=
  obind (bv_from_list n) (unpickle k).

Lemma bv_pickleK (n : nat) : pcancel (@bv_pickle n) (bv_unpickle n).
Proof.
  intro bv. unfold bv_pickle, bv_unpickle.
  rewrite pickleK. simpl.
  apply bv_pcancel.
Qed.

HB.instance Definition BVec_isCountable (n : nat) :=
  isCountable.Build (BVec n) (bv_pickleK n).

(* ============================= BelnapVec: bounded storage ============================= *)

Record BelnapVec (n : nat) :=
  mkBelnapVec {
      bv_val :> BVec n;
      _ : bv_bounded bv_val
    }.

Arguments bv_val {n} _.

Definition BelnapVec_rect n (K : BelnapVec n -> Type)
  (f : forall (v : BVec n) (h : bv_bounded v), K (@mkBelnapVec n v h))
  (u : BelnapVec n) : K u :=
  match u as u0 return (K u0) with
  | @mkBelnapVec _ v h => f v h
  end.

HB.instance Definition _ n :=
  @isSub.phant_Build _ _ _ (@bv_val n) (@mkBelnapVec n) (@BelnapVec_rect n) (fun _ _ => erefl).

HB.instance Definition _ n :=
  [Countable of BelnapVec n by <:].

(* ============================= BelnapVec operations ============================= *)

Definition bv_and {n} (a b : BelnapVec n) : BelnapVec n :=
  @mkBelnapVec n (vec_and a b) (bv_bounded_vec_and _ _ (valP a) (valP b)).

Definition bv_or {n} (a b : BelnapVec n) : BelnapVec n :=
  @mkBelnapVec n (vec_or a b) (bv_bounded_vec_or _ _ (valP a) (valP b)).

Definition bv_consensus {n} (a b : BelnapVec n) : BelnapVec n :=
  @mkBelnapVec n (vec_consensus a b) (bv_bounded_vec_consensus _ _ (valP a) (valP b)).

Definition bv_merge {n} (a b : BelnapVec n) : BelnapVec n :=
  @mkBelnapVec n (vec_merge a b) (bv_bounded_vec_merge _ _ (valP a) (valP b)).

(* ============================= BelnapVec constants ============================= *)

Definition bv_all_unknown (n : nat) : BelnapVec n :=
  @mkBelnapVec n (all_unknown n) (bv_bounded_all_unknown n).

Definition bv_all_both (n : nat) : BelnapVec n :=
  @mkBelnapVec n (all_both n) (bv_bounded_all_both n).

Definition bv_all_true (n : nat) : BelnapVec n :=
  @mkBelnapVec n (all_true n) (bv_bounded_all_true n).

Definition bv_all_false (n : nat) : BelnapVec n :=
  @mkBelnapVec n (all_false n) (bv_bounded_all_false n).

(* ============================= Newtype wrappers ============================= *)

Record AsTruth (n : nat) : Type :=
  mkAsTruth { unTruth :> BelnapVec n }.

Record AsKnowledge (n : nat) : Type :=
  mkAsKnowledge { unKnowledge :> BelnapVec n }.

Arguments unTruth {n} _.
Arguments unKnowledge {n} _.

(* isSub expects a two-argument eliminator (value + predicate proof), but these
   newtypes have no proof field.  We hand-write _rect to fabricate the trivial
   proof [isT : xpredT v].  Adding an actual [_ : xpredT] field to the record
   doesn't help: Rocq's auto-generated eliminator is a raw [match] with "no
   head constant", so the Sub_rect canonical projection is silently dropped. *)
Definition AsTruth_rect n (K : AsTruth n -> Type)
  (f : forall (v : BelnapVec n) (h : xpredT v), K (@mkAsTruth n v))
  (u : AsTruth n) : K u :=
  match u as u0 return (K u0) with
  | @mkAsTruth _ v => f v isT
  end.

Definition AsKnowledge_rect n (K : AsKnowledge n -> Type)
  (f : forall (v : BelnapVec n) (h : xpredT v), K (@mkAsKnowledge n v))
  (u : AsKnowledge n) : K u :=
  match u as u0 return (K u0) with
  | @mkAsKnowledge _ v => f v isT
  end.

HB.instance Definition _ n := [isSub for (unTruth : AsTruth n -> _) by AsTruth_rect n].
HB.instance Definition _ n := [isSub for (unKnowledge : AsKnowledge n -> _) by AsKnowledge_rect n].

HB.instance Definition _ n := [Countable of AsTruth n by <:].
HB.instance Definition _ n := [Countable of AsKnowledge n by <:].

(* ============================= Truth ordering ============================= *)

Fact truth_display : Order.disp_t. Proof. exact: (Order.Disp tt tt). Qed.
Fact know_display  : Order.disp_t. Proof. exact: (Order.Disp tt tt). Qed.

Definition truth_le {n : nat} (x y : AsTruth n) : bool :=
  (bv_and (unTruth x) (unTruth y) == unTruth x).

Definition truth_meet {n : nat} (x y : AsTruth n) : AsTruth n :=
  @mkAsTruth n (bv_and (unTruth x) (unTruth y)).

Definition truth_join {n : nat} (x y : AsTruth n) : AsTruth n :=
  @mkAsTruth n (bv_or (unTruth x) (unTruth y)).

Definition truth_bot (n : nat) : AsTruth n := @mkAsTruth n (bv_all_unknown n).
Definition truth_top (n : nat) : AsTruth n := @mkAsTruth n (bv_all_both n).

(* ============================= Knowledge ordering ============================= *)

Definition know_le {n : nat} (x y : AsKnowledge n) : bool :=
  (bv_consensus (unKnowledge x) (unKnowledge y) == unKnowledge x).

Definition know_meet {n : nat} (x y : AsKnowledge n) : AsKnowledge n :=
  @mkAsKnowledge n (bv_consensus (unKnowledge x) (unKnowledge y)).

Definition know_join {n : nat} (x y : AsKnowledge n) : AsKnowledge n :=
  @mkAsKnowledge n (bv_merge (unKnowledge x) (unKnowledge y)).

Definition know_bot (n : nat) : AsKnowledge n := @mkAsKnowledge n (bv_all_false n).
Definition know_top (n : nat) : AsKnowledge n := @mkAsKnowledge n (bv_all_true n).

(* ============================= Lattice law proofs ============================= *)

Lemma vec_and_comm {n} (a b : BVec n) : vec_and a b = vec_and b a.
Proof. apply vec_binop_storage_comm; exact N.land_comm. Qed.

Lemma vec_or_comm {n} (a b : BVec n) : vec_or a b = vec_or b a.
Proof. apply vec_binop_storage_comm; exact N.lor_comm. Qed.

Lemma vec_and_assoc {n} (a b c : BVec n) : vec_and a (vec_and b c) = vec_and (vec_and a b) c.
Proof. apply vec_binop_storage_assoc; exact N.land_assoc. Qed.

Lemma vec_or_assoc {n} (a b c : BVec n) : vec_or a (vec_or b c) = vec_or (vec_or a b) c.
Proof. apply vec_binop_storage_assoc; exact N.lor_assoc. Qed.

Lemma vec_consensus_comm {n} (a b : BVec n) : vec_consensus a b = vec_consensus b a.
Proof. apply vec_binop_storage_comm; [exact N.land_comm | exact N.lor_comm]. Qed.

Lemma vec_merge_comm {n} (a b : BVec n) : vec_merge a b = vec_merge b a.
Proof. apply vec_binop_storage_comm; [exact N.lor_comm | exact N.land_comm]. Qed.

Lemma vec_consensus_assoc {n} (a b c : BVec n) :
  vec_consensus a (vec_consensus b c) = vec_consensus (vec_consensus a b) c.
Proof. apply vec_binop_storage_assoc; [exact N.land_assoc | exact N.lor_assoc]. Qed.

Lemma vec_merge_assoc {n} (a b c : BVec n) :
  vec_merge a (vec_merge b c) = vec_merge (vec_merge a b) c.
Proof. apply vec_binop_storage_assoc; [exact N.lor_assoc | exact N.land_assoc]. Qed.

Lemma vec_and_vec_or_abs {n} (a b : BVec n) : vec_and a (vec_or a b) = a.
Proof. apply vec_binop_storage_absorb; exact N_land_lor_diag. Qed.

Lemma vec_or_vec_and_abs {n} (a b : BVec n) : vec_or a (vec_and a b) = a.
Proof. apply vec_binop_storage_absorb; exact N_lor_land_diag. Qed.

Lemma vec_consensus_vec_merge_abs {n} (a b : BVec n) : vec_consensus a (vec_merge a b) = a.
Proof. apply vec_binop_storage_absorb; [exact N_land_lor_diag | exact N_lor_land_diag]. Qed.

Lemma vec_merge_vec_consensus_abs {n} (a b : BVec n) : vec_merge a (vec_consensus a b) = a.
Proof. apply vec_binop_storage_absorb; [exact N_lor_land_diag | exact N_land_lor_diag]. Qed.

Lemma vec_and_idem {n} (v : BVec n) : vec_and v v = v.
Proof. exact (vec_binop_storage_idem _ _ N.land_diag N.land_diag v). Qed.

Lemma vec_consensus_idem {n} (v : BVec n) : vec_consensus v v = v.
Proof. exact (vec_binop_storage_idem _ _ N.land_diag N.lor_diag v). Qed.

(* ============================= BelnapVec algebraic laws ============================= *)

Lemma bv_and_idem {n} (x : BelnapVec n) : bv_and x x = x.
Proof. apply val_inj. apply vec_and_idem. Qed.

Lemma bv_consensus_idem {n} (x : BelnapVec n) : bv_consensus x x = x.
Proof. apply val_inj. apply vec_consensus_idem. Qed.

Lemma bv_and_comm {n} (a b : BelnapVec n) : bv_and a b = bv_and b a.
Proof. apply val_inj. apply vec_and_comm. Qed.

Lemma bv_or_comm {n} (a b : BelnapVec n) : bv_or a b = bv_or b a.
Proof. apply val_inj. apply vec_or_comm. Qed.

Lemma bv_consensus_comm {n} (a b : BelnapVec n) : bv_consensus a b = bv_consensus b a.
Proof. apply val_inj. apply vec_consensus_comm. Qed.

Lemma bv_merge_comm {n} (a b : BelnapVec n) : bv_merge a b = bv_merge b a.
Proof. apply val_inj. apply vec_merge_comm. Qed.

Lemma bv_and_assoc {n} (a b c : BelnapVec n) :
  bv_and a (bv_and b c) = bv_and (bv_and a b) c.
Proof. apply val_inj. simpl. apply vec_and_assoc. Qed.

Lemma bv_or_assoc {n} (a b c : BelnapVec n) :
  bv_or a (bv_or b c) = bv_or (bv_or a b) c.
Proof. apply val_inj. simpl. apply vec_or_assoc. Qed.

Lemma bv_consensus_assoc {n} (a b c : BelnapVec n) :
  bv_consensus a (bv_consensus b c) = bv_consensus (bv_consensus a b) c.
Proof. apply val_inj. simpl. apply vec_consensus_assoc. Qed.

Lemma bv_merge_assoc {n} (a b c : BelnapVec n) :
  bv_merge a (bv_merge b c) = bv_merge (bv_merge a b) c.
Proof. apply val_inj. simpl. apply vec_merge_assoc. Qed.

Lemma bv_and_or_abs {n} (a b : BelnapVec n) : bv_and a (bv_or a b) = a.
Proof. apply val_inj. simpl. apply vec_and_vec_or_abs. Qed.

Lemma bv_or_and_abs {n} (a b : BelnapVec n) : bv_or a (bv_and a b) = a.
Proof. apply val_inj. simpl. apply vec_or_vec_and_abs. Qed.

Lemma bv_consensus_merge_abs {n} (a b : BelnapVec n) :
  bv_consensus a (bv_merge a b) = a.
Proof. apply val_inj. simpl. apply vec_consensus_vec_merge_abs. Qed.

Lemma bv_merge_consensus_abs {n} (a b : BelnapVec n) :
  bv_merge a (bv_consensus a b) = a.
Proof. apply val_inj. simpl. apply vec_merge_vec_consensus_abs. Qed.

Lemma bv_and_all_unknown_l {n} (x : BelnapVec n) :
  bv_and (bv_all_unknown n) x = bv_all_unknown n.
Proof. apply val_inj. simpl. apply vec_and_all_unknown_l. Qed.

Lemma bv_and_all_both_r {n} (x : BelnapVec n) :
  bv_and x (bv_all_both n) = x.
Proof. apply val_inj. simpl. apply vec_and_all_both_r. exact (valP x). Qed.

Lemma bv_consensus_all_false_l {n} (x : BelnapVec n) :
  bv_consensus (bv_all_false n) x = bv_all_false n.
Proof. apply val_inj. simpl. apply vec_consensus_all_false_l. exact (valP x). Qed.

Lemma bv_consensus_all_true_r {n} (x : BelnapVec n) :
  bv_consensus x (bv_all_true n) = x.
Proof. apply val_inj. simpl. apply vec_consensus_all_true_r. exact (valP x). Qed.

(* ============================= Order proofs ============================= *)

Lemma truth_le_refl {n} (x : AsTruth n) : truth_le x x.
Proof. apply/eqP. apply bv_and_idem. Qed.

Lemma truth_le_anti {n} : antisymmetric (@truth_le n).
Proof.
  move=> x y /andP [/eqP Hxy /eqP Hyx].
  have : unTruth x = unTruth y by rewrite -Hxy bv_and_comm.
  exact: val_inj.
Qed.

Lemma truth_le_trans {n} : transitive (@truth_le n).
Proof.
  move=> y x z /eqP Hxy /eqP Hyz.
  apply/eqP. rewrite -{1}(Hxy) -bv_and_assoc Hyz. exact Hxy.
Qed.

Lemma truth_leEmeet {n} (x y : AsTruth n) :
  truth_le x y = (truth_meet x y == x).
Proof. reflexivity. Qed.

(* ============================= MathComp HB lattice instances for AsTruth ============================= *)

Lemma truth_meetC {n} : commutative (@truth_meet n).
Proof. intros x y. apply val_inj. apply bv_and_comm. Qed.

Lemma truth_joinC {n} : commutative (@truth_join n).
Proof. intros x y. apply val_inj. apply bv_or_comm. Qed.

Lemma truth_meetA {n} : associative (@truth_meet n).
Proof. intros x y z. apply val_inj. simpl. apply bv_and_assoc. Qed.

Lemma truth_joinA {n} : associative (@truth_join n).
Proof. intros x y z. apply val_inj. simpl. apply bv_or_assoc. Qed.

Lemma truth_joinKI {n} (y x : AsTruth n) : truth_meet x (truth_join x y) = x.
Proof. apply val_inj. simpl. apply bv_and_or_abs. Qed.

Lemma truth_meetKU {n} (y x : AsTruth n) : truth_join x (truth_meet x y) = x.
Proof. apply val_inj. simpl. apply bv_or_and_abs. Qed.

HB.instance Definition _ (n : nat) :=
  Order.Le_isPOrder.Build truth_display (AsTruth n)
    (@truth_le_refl n) (@truth_le_anti n) (@truth_le_trans n).

HB.instance Definition _ (n : nat) :=
  Order.POrder_isLattice.Build truth_display (AsTruth n)
    (@truth_meetC n) (@truth_joinC n)
    (@truth_meetA n) (@truth_joinA n)
    (@truth_joinKI n) (@truth_meetKU n)
    (@truth_leEmeet n).

Lemma truth_le0x {n} (x : AsTruth n) : truth_le (truth_bot n) x.
Proof. apply/eqP. apply bv_and_all_unknown_l. Qed.

Lemma truth_lex1 {n} (x : AsTruth n) : truth_le x (truth_top n).
Proof. apply/eqP. apply bv_and_all_both_r. Qed.

HB.instance Definition _ (n : nat) :=
  Order.hasBottom.Build truth_display (AsTruth n) (@truth_le0x n).

HB.instance Definition _ (n : nat) :=
  Order.hasTop.Build truth_display (AsTruth n) (@truth_lex1 n).

(* ============================= Knowledge ordering proofs ============================= *)

Lemma know_le_refl {n} (x : AsKnowledge n) : know_le x x.
Proof. apply/eqP. apply bv_consensus_idem. Qed.

Lemma know_le_anti {n} : antisymmetric (@know_le n).
Proof.
  move=> x y /andP [/eqP Hxy /eqP Hyx].
  have : unKnowledge x = unKnowledge y by rewrite -Hxy bv_consensus_comm.
  exact: val_inj.
Qed.

Lemma know_le_trans {n} : transitive (@know_le n).
Proof.
  move=> y x z /eqP Hxy /eqP Hyz.
  apply/eqP. rewrite -{1}(Hxy) -bv_consensus_assoc Hyz. exact Hxy.
Qed.

Lemma know_leEmeet {n} (x y : AsKnowledge n) :
  know_le x y = (know_meet x y == x).
Proof. reflexivity. Qed.

Lemma know_meetC {n} : commutative (@know_meet n).
Proof. intros x y. apply val_inj. apply bv_consensus_comm. Qed.

Lemma know_joinC {n} : commutative (@know_join n).
Proof. intros x y. apply val_inj. apply bv_merge_comm. Qed.

Lemma know_meetA {n} : associative (@know_meet n).
Proof. intros x y z. apply val_inj. simpl. apply bv_consensus_assoc. Qed.

Lemma know_joinA {n} : associative (@know_join n).
Proof. intros x y z. apply val_inj. simpl. apply bv_merge_assoc. Qed.

Lemma know_joinKI {n} (y x : AsKnowledge n) : know_meet x (know_join x y) = x.
Proof. apply val_inj. simpl. apply bv_consensus_merge_abs. Qed.

Lemma know_meetKU {n} (y x : AsKnowledge n) : know_join x (know_meet x y) = x.
Proof. apply val_inj. simpl. apply bv_merge_consensus_abs. Qed.

Lemma know_le0x {n} (x : AsKnowledge n) : know_le (know_bot n) x.
Proof. apply/eqP. apply bv_consensus_all_false_l. Qed.

Lemma know_lex1 {n} (x : AsKnowledge n) : know_le x (know_top n).
Proof. apply/eqP. apply bv_consensus_all_true_r. Qed.

HB.instance Definition _ (n : nat) :=
  Order.Le_isPOrder.Build know_display (AsKnowledge n)
    (@know_le_refl n) (@know_le_anti n) (@know_le_trans n).

HB.instance Definition _ (n : nat) :=
  Order.POrder_isLattice.Build know_display (AsKnowledge n)
    (@know_meetC n) (@know_joinC n)
    (@know_meetA n) (@know_joinA n)
    (@know_joinKI n) (@know_meetKU n)
    (@know_leEmeet n).

HB.instance Definition _ (n : nat) :=
  Order.hasBottom.Build know_display (AsKnowledge n) (@know_le0x n).

HB.instance Definition _ (n : nat) :=
  Order.hasTop.Build know_display (AsKnowledge n) (@know_lex1 n).
