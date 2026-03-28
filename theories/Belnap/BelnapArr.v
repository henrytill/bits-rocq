Set Warnings "-stdlib-vector".
Set Warnings "-notation-overridden".

From Stdlib Require Import NArith Arith Lia ZArith.
From Stdlib Require Import Vectors.Vector Vectors.Fin.
From Stdlib Require Import PrimArray ArrayAxioms Uint63.
Import PArrayNotations.

From Equations Require Import Equations.
From Bits.Belnap Require Import BelnapModel.

(* ============================= PArray universe fix ============================= *)

(** The ArrayAxioms lemmas ([length_make], [get_set_same], etc.) are not
    universe-polymorphic, so [rewrite length_make] fails when the element
    type lives in [Set] (e.g. [N]).  We redeclare them as polymorphic axioms. *)
#[universes(polymorphic)] Axiom length_make_ :
  forall (A : Type) (size : int) (a : A),
    length (make size a) = if (size <=? max_length)%uint63 then size else max_length.

#[universes(polymorphic)] Axiom get_make_ :
  forall (A : Type) (a : A) (size i : int),
    (make size a).[i] = a.

#[universes(polymorphic)] Axiom get_set_same_ :
  forall (A : Type) (t : array A) (i : int) (a : A),
    (i <? length t)%uint63 = true -> t.[i <- a].[i] = a.

#[universes(polymorphic)] Axiom get_set_other_ :
  forall (A : Type) (t : array A) (i j : int) (a : A),
    i <> j -> t.[i <- a].[j] = t.[j].

#[universes(polymorphic)] Axiom length_set_ :
  forall (A : Type) (t : array A) (i : int) (a : A),
    length t.[i <- a] = length t.

(* ============================= Fin_to_int63 ============================= *)

Definition Fin_to_int63 {m : nat} (i : Fin.t m) : int :=
  of_nat (fin_val i).

(* ============================= Size bound ============================= *)

(** We require [storage_size n] to fit in a PArray.  This is always true for
    practical [n] (up to ~2^62 elements). *)
Definition size_fits (n : nat) : Prop :=
  (Z.of_nat (storage_size n) <= to_Z max_length)%Z.

Section WithBound.

  Variable n : nat.
  Hypothesis Hn : size_fits n.

  (** [of_nat] is injective on values below [wB]. *)
  Lemma to_Z_of_nat_small (k : nat) (Hk : (Z.of_nat k < wB)%Z) :
    to_Z (of_nat k) = Z.of_nat k.
  Proof.
    rewrite of_Z_spec.
    rewrite Z.mod_small; [reflexivity | lia].
  Qed.

  Lemma storage_size_lt_wB : (Z.of_nat (storage_size n) < wB)%Z.
  Proof.
    unfold size_fits in Hn.
    pose proof (to_Z_bounded max_length) as [_ Hmax]. lia.
  Qed.

  Lemma size_fits_leb : (of_nat (storage_size n) <=? max_length)%uint63 = true.
  Proof.
    apply leb_spec. rewrite to_Z_of_nat_small by apply storage_size_lt_wB.
    exact Hn.
  Qed.

  Lemma fin_val_lt_wB (m : nat) (Hm : (Z.of_nat m < wB)%Z) (i : Fin.t m) :
    (Z.of_nat (fin_val i) < wB)%Z.
  Proof.
    pose proof (fin_lt i).
    apply Nat2Z.inj_lt in H. lia.
  Qed.

  Lemma of_nat_lt_compat (a b : nat)
    (Ha : (Z.of_nat a < wB)%Z) (Hb : (Z.of_nat b < wB)%Z) :
    a < b -> (of_nat a <? of_nat b)%uint63 = true.
  Proof.
    intro Hab. apply ltb_spec.
    rewrite !to_Z_of_nat_small by assumption. lia.
  Qed.

  Lemma of_nat_inj (a b : nat)
    (Ha : (Z.of_nat a < wB)%Z) (Hb : (Z.of_nat b < wB)%Z) :
    of_nat a = of_nat b -> a = b.
  Proof.
    intro H. apply (f_equal to_Z) in H.
    rewrite !to_Z_of_nat_small in H by assumption. lia.
  Qed.

  Lemma Fin_to_int63_in_bounds (i : Fin.t (storage_size n)) (arr : array N)
    (Hlen : length arr = of_nat (storage_size n)) :
    (Fin_to_int63 i <? length arr)%uint63 = true.
  Proof.
    rewrite Hlen. unfold Fin_to_int63.
    apply of_nat_lt_compat.
    - apply fin_val_lt_wB. exact storage_size_lt_wB.
    - exact storage_size_lt_wB.
    - exact (fin_lt i).
  Qed.

  Lemma Fin_to_int63_inj (i j : Fin.t (storage_size n)) :
    Fin_to_int63 i = Fin_to_int63 j -> fin_val i = fin_val j.
  Proof.
    apply of_nat_inj.
    - apply fin_val_lt_wB. exact storage_size_lt_wB.
    - apply fin_val_lt_wB. exact storage_size_lt_wB.
  Qed.

  (* ============================= BelnapArr record ============================= *)

  Record BelnapArr : Type := mkBelnapArr {
                                 store : array N;
                                 hlen  : length store = of_nat (storage_size n)
                               }.

  (* ============================= Simulation relation ============================= *)

  Local Notation BVec := (Vector.t N (storage_size n)).

  Definition models (bv : BVec) (ba : BelnapArr) : Prop :=
    forall (i : Fin.t (storage_size n)),
      Vector.nth bv i = get (store ba) (Fin_to_int63 i).

  (* ============================= Constants ============================= *)

  Lemma make_length (v : N) :
    length (make (of_nat (storage_size n)) v) = of_nat (storage_size n).
  Proof. rewrite length_make_. rewrite size_fits_leb. reflexivity. Qed.

  Definition ba_all_unknown : BelnapArr :=
    mkBelnapArr (make (of_nat (storage_size n)) 0%N) (make_length _).

  Definition ba_all_both : BelnapArr :=
    mkBelnapArr (make (of_nat (storage_size n)) (N.ones 64)) (make_length _).

  Lemma ba_all_unknown_models : models (all_unknown n) ba_all_unknown.
  Proof.
    intro i. unfold models, all_unknown, ba_all_unknown. simpl.
    rewrite Vector.const_nth. rewrite get_make_. reflexivity.
  Qed.

  Lemma ba_all_both_models : models (all_both n) ba_all_both.
  Proof.
    intro i. unfold models, all_both, ba_all_both. simpl.
    rewrite Vector.const_nth. rewrite get_make_. reflexivity.
  Qed.

  (* ============================= PArray imap2 ============================= *)

  (** Build a new array by applying [f idx] pointwise to two source arrays,
      counting down from [fuel] to 0.  When [f] ignores its index argument
      this degenerates to a plain map2. *)
  Fixpoint parray_imap2_aux (f : nat -> N -> N -> N) (a b result : array N)
    (fuel : nat) : array N :=
    match fuel with
    | O => result
    | S fuel' =>
        let idx := of_nat fuel' in
        parray_imap2_aux f a b
          (set result idx (f fuel' (get a idx) (get b idx)))
          fuel'
    end.

  Definition parray_imap2 (f : nat -> N -> N -> N) (a b : array N)
    (sz : nat) (dflt : N) : array N :=
    parray_imap2_aux f a b (make (of_nat sz) dflt) sz.

  (* ============================= parray_imap2 length preservation ============================= *)

  Lemma parray_imap2_aux_length (f : nat -> N -> N -> N) (a b result : array N) (fuel : nat) :
    length (parray_imap2_aux f a b result fuel) = length result.
  Proof.
    revert result. induction fuel as [|fuel' IH]; intro result.
    - reflexivity.
    - simpl. rewrite IH. rewrite length_set_. reflexivity.
  Qed.

  Lemma parray_imap2_length (f : nat -> N -> N -> N) (a b : array N)
    (sz : nat) (dflt : N) :
    (of_nat sz <=? max_length)%uint63 = true ->
    length (parray_imap2 f a b sz dflt) = of_nat sz.
  Proof.
    intro Hsz. unfold parray_imap2.
    rewrite parray_imap2_aux_length.
    rewrite length_make_. rewrite Hsz. reflexivity.
  Qed.

  (* ============================= parray_imap2_aux simulation ============================= *)

  (** Indices at [fuel] or above are untouched. *)
  Lemma parray_imap2_aux_get_hi (f : nat -> N -> N -> N) (a b result : array N) (fuel : nat)
    (k : nat) (Hk : fuel <= k) (HkwB : (Z.of_nat k < wB)%Z)
    (HfuelwB : (Z.of_nat fuel < wB)%Z) :
    get (parray_imap2_aux f a b result fuel) (of_nat k) = get result (of_nat k).
  Proof.
    revert result. induction fuel as [|fuel' IH]; intro result.
    - reflexivity.
    - simpl. rewrite IH by lia.
      rewrite get_set_other_; [reflexivity|].
      intro Heq. apply of_nat_inj in Heq; lia.
  Qed.

  Lemma parray_imap2_aux_get (f : nat -> N -> N -> N) (a b result : array N)
    (fuel sz : nat) (Hfs : fuel <= sz)
    (k : nat) (Hk : k < fuel) (HkwB : (Z.of_nat k < wB)%Z)
    (HszwB : (Z.of_nat sz < wB)%Z)
    (Hlen : length result = of_nat sz) :
    get (parray_imap2_aux f a b result fuel) (of_nat k) =
      f k (get a (of_nat k)) (get b (of_nat k)).
  Proof.
    revert k Hk HkwB result Hlen.
    induction fuel as [|fuel' IH]; intros k Hk HkwB result Hlen.
    - lia.
    - simpl. destruct (Nat.eq_dec k fuel') as [->|Hne].
      + rewrite parray_imap2_aux_get_hi by lia.
        apply get_set_same_. rewrite Hlen.
        apply of_nat_lt_compat; lia.
      + apply IH; try lia. rewrite length_set_. exact Hlen.
  Qed.

  Lemma parray_imap2_get (f : nat -> N -> N -> N) (a b : array N)
    (sz : nat) (dflt : N) (k : nat)
    (Hk : k < sz) (HszwB : (Z.of_nat sz < wB)%Z)
    (Hleb : (of_nat sz <=? max_length)%uint63 = true) :
    get (parray_imap2 f a b sz dflt) (of_nat k) =
      f k (get a (of_nat k)) (get b (of_nat k)).
  Proof.
    unfold parray_imap2.
    apply parray_imap2_aux_get with (sz := sz); try lia.
    rewrite length_make_. rewrite Hleb. reflexivity.
  Qed.

  (* ============================= BelnapArr bulk operations ============================= *)

  Definition ba_binop_storage_f (posOp negOp : N -> N -> N) (idx : nat) : N -> N -> N :=
    if Nat.even idx then posOp else negOp.

  Definition ba_binop (posOp negOp : N -> N -> N) (a b : BelnapArr) : BelnapArr :=
    let f := ba_binop_storage_f posOp negOp in
    let arr := parray_imap2 f (store a) (store b) (storage_size n) 0%N in
    mkBelnapArr arr (parray_imap2_length f _ _ _ _ size_fits_leb).

  Definition ba_and       := ba_binop N.land N.land.
  Definition ba_or        := ba_binop N.lor  N.lor.
  Definition ba_consensus := ba_binop N.land N.lor.
  Definition ba_merge     := ba_binop N.lor  N.land.

  (* ============================= BelnapArr element access ============================= *)

  Definition ba_get (i : Fin.t n) (ba : BelnapArr) : Belnap :=
    let b := bit_index i in
    let posW := get (store ba) (Fin_to_int63 (pos_word_fin i)) in
    let negW := get (store ba) (Fin_to_int63 (neg_word_fin i)) in
    decode_belnap (N.land (N.shiftr posW (N.of_nat b)) 1%N)
      (N.land (N.shiftr negW (N.of_nat b)) 1%N).

  Lemma set_length (arr : array N) (i : int) (v : N) :
    length arr = of_nat (storage_size n) ->
    length (set arr i v) = of_nat (storage_size n).
  Proof. intro H. rewrite length_set_. exact H. Qed.

  Definition ba_set (i : Fin.t n) (b : Belnap) (ba : BelnapArr) : BelnapArr :=
    let bit := bit_index i in
    let bitMask := N.lnot (N.shiftl 1%N (N.of_nat bit)) 64%N in
    let '(posBit, negBit) := encode_belnap b bit in
    let s1 := set (store ba) (Fin_to_int63 (pos_word_fin i))
                (N.lor (N.land (get (store ba) (Fin_to_int63 (pos_word_fin i))) bitMask) posBit) in
    let s2 := set s1 (Fin_to_int63 (neg_word_fin i))
                (N.lor (N.land (get s1 (Fin_to_int63 (neg_word_fin i))) bitMask) negBit) in
    mkBelnapArr s2 (set_length _ _ _ (set_length _ _ _ (hlen ba))).

  (* ============================= BelnapArr negation ============================= *)

  (** Swap even/odd word pairs. *)
  Fixpoint parray_swap_aux (src result : array N) (fuel : nat) : array N :=
    match fuel with
    | O => result
    | S fuel' =>
        let base := 2 * fuel' in
        let i_even := of_nat base in
        let i_odd := of_nat (base + 1) in
        let result' := set (set result i_even (get src i_odd)) i_odd (get src i_even) in
        parray_swap_aux src result' fuel'
    end.

  Lemma parray_swap_aux_length (src result : array N) (fuel : nat) :
    length (parray_swap_aux src result fuel) = length result.
  Proof.
    revert result. induction fuel as [|fuel' IH]; intro result.
    - reflexivity.
    - simpl. rewrite IH. rewrite !length_set_. reflexivity.
  Qed.

  Lemma ba_not_length (ba : BelnapArr) :
    length (parray_swap_aux (store ba) (make (of_nat (storage_size n)) 0%N)
              (words_per_plane n)) = of_nat (storage_size n).
  Proof.
    rewrite parray_swap_aux_length. rewrite length_make_.
    rewrite size_fits_leb. reflexivity.
  Qed.

  (** High-index preservation for swap: indices at [2*fuel] or above are untouched. *)
  Lemma parray_swap_aux_get_hi (src result : array N) (fuel : nat)
    (k : nat) (Hk : 2 * fuel <= k) (HkwB : (Z.of_nat k < wB)%Z)
    (HfuelwB : (Z.of_nat (2 * fuel) < wB)%Z) :
    get (parray_swap_aux src result fuel) (of_nat k) = get result (of_nat k).
  Proof.
    revert result. induction fuel as [|fuel' IH]; intro result.
    - reflexivity.
    - simpl. rewrite IH by lia.
      rewrite get_set_other_; [|intro Heq; apply of_nat_inj in Heq; lia].
      rewrite get_set_other_; [reflexivity|intro Heq; apply of_nat_inj in Heq; lia].
  Qed.

  (** After processing all pairs, index [k] has the swapped value. *)
  Lemma parray_swap_aux_get (src result : array N)
    (fuel sz : nat) (Hfs : 2 * fuel <= sz)
    (k : nat) (Hk : k < 2 * fuel) (HkwB : (Z.of_nat k < wB)%Z)
    (HszwB : (Z.of_nat sz < wB)%Z)
    (Hlen : length result = of_nat sz) :
    get (parray_swap_aux src result fuel) (of_nat k) =
      if Nat.even k then get src (of_nat (k + 1)) else get src (of_nat (k - 1)).
  Proof.
    revert k Hk HkwB result Hlen.
    induction fuel as [|fuel' IH]; intros k Hk HkwB result Hlen.
    - lia.
    - simpl.
      destruct (Nat.eq_dec k (2 * fuel')) as [->|Hne_even].
      + rewrite parray_swap_aux_get_hi by lia.
        rewrite get_set_other_; [|intro Heq; apply of_nat_inj in Heq; lia].
        rewrite get_set_same_.
        * replace (Nat.even (2 * fuel')) with true
            by (symmetry; apply Nat.even_mul; left; reflexivity).
          reflexivity.
        * rewrite Hlen. apply of_nat_lt_compat; lia.
      + destruct (Nat.eq_dec k (2 * fuel' + 1)) as [->|Hne_odd].
        * rewrite parray_swap_aux_get_hi by lia.
          rewrite get_set_same_.
          -- replace (Nat.even (2 * fuel' + 1)) with false.
             ++ replace (2 * fuel' + 1 - 1) with (2 * fuel') by lia. reflexivity.
             ++ symmetry. rewrite Nat.even_add.
                replace (Nat.even (2 * fuel')) with true
                  by (symmetry; apply Nat.even_mul; left; reflexivity).
                reflexivity.
          -- rewrite length_set_. rewrite Hlen. apply of_nat_lt_compat; lia.
        * apply IH; try lia. rewrite !length_set_. exact Hlen.
  Qed.

  Lemma parray_swap_get (src : array N)
    (k : nat) (Hk : k < storage_size n) :
    get (parray_swap_aux src (make (of_nat (storage_size n)) 0%N) (words_per_plane n)) (of_nat k) =
      if Nat.even k then get src (of_nat (k + 1)) else get src (of_nat (k - 1)).
  Proof.
    apply parray_swap_aux_get with (sz := storage_size n).
    - unfold storage_size. rewrite double_eq_mul2. lia.
    - unfold storage_size in Hk. rewrite double_eq_mul2 in Hk. lia.
    - pose proof storage_size_lt_wB. lia.
    - exact storage_size_lt_wB.
    - rewrite length_make_. rewrite size_fits_leb. reflexivity.
  Qed.

  Definition ba_not (ba : BelnapArr) : BelnapArr :=
    mkBelnapArr (parray_swap_aux (store ba) (make (of_nat (storage_size n)) 0%N)
                   (words_per_plane n))
      (ba_not_length ba).

  (* ============================= Interleaved constant construction ============================= *)

  (** Build an array with [even_val] at even indices and [odd_val] at odd indices. *)
  Fixpoint parray_interleave_aux (even_val odd_val : N) (result : array N)
    (fuel : nat) : array N :=
    match fuel with
    | O => result
    | S fuel' =>
        let base := 2 * fuel' in
        let result' := set (set result (of_nat base) even_val)
                         (of_nat (base + 1)) odd_val in
        parray_interleave_aux even_val odd_val result' fuel'
    end.

  Definition parray_interleave (even_val odd_val : N) : array N :=
    parray_interleave_aux even_val odd_val
      (make (of_nat (storage_size n)) 0%N) (words_per_plane n).

  Lemma parray_interleave_aux_length (ev ov : N) (result : array N) (fuel : nat) :
    length (parray_interleave_aux ev ov result fuel) = length result.
  Proof.
    revert result. induction fuel as [|fuel' IH]; intro result.
    - reflexivity.
    - simpl. rewrite IH. rewrite !length_set_. reflexivity.
  Qed.

  Lemma parray_interleave_length (ev ov : N) :
    length (parray_interleave ev ov) = of_nat (storage_size n).
  Proof.
    unfold parray_interleave.
    rewrite parray_interleave_aux_length.
    rewrite length_make_. rewrite size_fits_leb. reflexivity.
  Qed.

  (** High-index preservation: indices at [2*fuel] or above are untouched. *)
  Lemma parray_interleave_aux_get_hi (ev ov : N) (result : array N) (fuel : nat)
    (k : nat) (Hk : 2 * fuel <= k) (HkwB : (Z.of_nat k < wB)%Z)
    (HfuelwB : (Z.of_nat (2 * fuel) < wB)%Z) :
    get (parray_interleave_aux ev ov result fuel) (of_nat k) = get result (of_nat k).
  Proof.
    revert result. induction fuel as [|fuel' IH]; intro result.
    - reflexivity.
    - simpl. rewrite IH by lia.
      rewrite get_set_other_; [|intro Heq; apply of_nat_inj in Heq; lia].
      rewrite get_set_other_; [reflexivity|intro Heq; apply of_nat_inj in Heq; lia].
  Qed.

  (** After processing all pairs [0..fuel-1], index [k] has the interleaved value. *)
  Lemma parray_interleave_aux_get (ev ov : N) (result : array N)
    (fuel sz : nat) (Hfs : 2 * fuel <= sz)
    (k : nat) (Hk : k < 2 * fuel) (HkwB : (Z.of_nat k < wB)%Z)
    (HszwB : (Z.of_nat sz < wB)%Z)
    (Hlen : length result = of_nat sz) :
    get (parray_interleave_aux ev ov result fuel) (of_nat k) =
      if Nat.even k then ev else ov.
  Proof.
    revert k Hk HkwB result Hlen.
    induction fuel as [|fuel' IH]; intros k Hk HkwB result Hlen.
    - lia.
    - simpl.
      destruct (Nat.eq_dec k (2 * fuel')) as [->|Hne_even].
      + (* k = 2 * fuel', the even index of this pair *)
        rewrite parray_interleave_aux_get_hi by lia.
        rewrite get_set_other_; [|intro Heq; apply of_nat_inj in Heq; lia].
        rewrite get_set_same_.
        * replace (Nat.even (2 * fuel')) with true by (symmetry; apply Nat.even_mul; left; reflexivity).
          reflexivity.
        * rewrite Hlen. apply of_nat_lt_compat; lia.
      + destruct (Nat.eq_dec k (2 * fuel' + 1)) as [->|Hne_odd].
        * (* k = 2 * fuel' + 1, the odd index of this pair *)
          rewrite parray_interleave_aux_get_hi by lia.
          rewrite get_set_same_.
          -- replace (Nat.even (2 * fuel' + 1)) with false.
             ++ reflexivity.
             ++ symmetry. rewrite Nat.even_add.
                replace (Nat.even (2 * fuel')) with true by (symmetry; apply Nat.even_mul; left; reflexivity).
                reflexivity.
          -- rewrite length_set_. rewrite Hlen. apply of_nat_lt_compat; lia.
        * (* k < 2 * fuel', recurse *)
          apply IH; try lia. rewrite !length_set_. exact Hlen.
  Qed.

  Lemma parray_interleave_get (ev ov : N) (k : nat)
    (Hk : k < storage_size n) :
    get (parray_interleave ev ov) (of_nat k) =
      if Nat.even k then ev else ov.
  Proof.
    unfold parray_interleave.
    apply parray_interleave_aux_get with (sz := storage_size n).
    - unfold storage_size. rewrite double_eq_mul2. lia.
    - unfold storage_size in Hk. rewrite double_eq_mul2 in Hk. lia.
    - pose proof storage_size_lt_wB. lia.
    - exact storage_size_lt_wB.
    - rewrite length_make_. rewrite size_fits_leb. reflexivity.
  Qed.

  Definition ba_all_true : BelnapArr :=
    mkBelnapArr (parray_interleave (N.ones 64) 0%N) (parray_interleave_length _ _).

  Definition ba_all_false : BelnapArr :=
    mkBelnapArr (parray_interleave 0%N (N.ones 64)) (parray_interleave_length _ _).

  (* ============================= Simulation: ba_get ============================= *)

  Lemma ba_get_models (i : Fin.t n) (bv : BVec) (ba : BelnapArr) :
    models bv ba -> ba_get i ba = bv_get i bv.
  Proof.
    intro Hmod. unfold ba_get, bv_get.
    rewrite <- (Hmod (pos_word_fin i)).
    rewrite <- (Hmod (neg_word_fin i)).
    reflexivity.
  Qed.

  (* ============================= Simulation: ba_set ============================= *)

  (** pos_word_fin and neg_word_fin always differ: one is even, the other odd. *)
  Lemma pos_neg_word_fin_neq (i : Fin.t n) : pos_word_fin i <> neg_word_fin i.
  Proof.
    intro H. apply (f_equal (fun j => fin_val j)) in H.
    unfold pos_word_fin, neg_word_fin in H.
    rewrite !fin_val_of_nat_lt in H. lia.
  Qed.

  Lemma Fin_to_int63_neq (a b : Fin.t (storage_size n)) :
    a <> b -> Fin_to_int63 a <> Fin_to_int63 b.
  Proof.
    intros Hne Heq. apply Hne. apply fin_val_inj. exact (Fin_to_int63_inj _ _ Heq).
  Qed.

  Lemma ba_set_models (i : Fin.t n) (b : Belnap) (bv : BVec) (ba : BelnapArr) :
    models bv ba ->
    models (bv_set i b bv) (ba_set i b ba).
  Proof.
    intro Hmod. intro j. unfold ba_set, bv_set.
    set (bit := bit_index i).
    set (bitMask := N.lnot (N.shiftl 1%N (N.of_nat bit)) 64%N).
    destruct (encode_belnap b bit) as [posBit negBit] eqn:Henc.
    simpl.
    pose proof (pos_neg_word_fin_neq i) as Hpn.
    destruct (Fin.eq_dec j (neg_word_fin i)) as [Heq_neg|Hne_neg].
    - subst j.
      rewrite get_set_same_ by (rewrite length_set_; apply Fin_to_int63_in_bounds; exact (hlen ba)).
      rewrite Vector.nth_replace_eq.
      rewrite get_set_other_ by (apply Fin_to_int63_neq; exact Hpn).
      rewrite <- (Hmod (neg_word_fin i)).
      rewrite Vector.nth_replace_neq by exact (not_eq_sym Hpn).
      reflexivity.
    - rewrite get_set_other_ by (apply Fin_to_int63_neq; exact (not_eq_sym Hne_neg)).
      rewrite Vector.nth_replace_neq by exact Hne_neg.
      destruct (Fin.eq_dec j (pos_word_fin i)) as [Heq_pos|Hne_pos].
      + subst j.
        rewrite get_set_same_ by (apply Fin_to_int63_in_bounds; exact (hlen ba)).
        rewrite Vector.nth_replace_eq.
        rewrite <- (Hmod (pos_word_fin i)). reflexivity.
      + rewrite get_set_other_ by (apply Fin_to_int63_neq; exact (not_eq_sym Hne_pos)).
        rewrite Vector.nth_replace_neq by exact Hne_pos.
        apply Hmod.
  Qed.

  (* ============================= Simulation: bulk binops ============================= *)

  Lemma ba_binop_models (posOp negOp : N -> N -> N)
    (bv1 bv2 : BVec) (ba1 ba2 : BelnapArr) :
    models bv1 ba1 -> models bv2 ba2 ->
    models (vec_binop_storage posOp negOp bv1 bv2) (ba_binop posOp negOp ba1 ba2).
  Proof.
    intros Hmod1 Hmod2 i.
    unfold ba_binop; simpl; unfold Fin_to_int63.
    rewrite (parray_imap2_get _ _ _ _ _ (fin_val i) (fin_lt i)
               storage_size_lt_wB size_fits_leb).
    rewrite vec_binop_storage_nth.
    unfold ba_binop_storage_f.
    destruct (Nat.even (fin_val i)); rewrite Hmod1, Hmod2; reflexivity.
  Qed.

  Definition ba_and_models       := ba_binop_models N.land N.land.
  Definition ba_or_models        := ba_binop_models N.lor  N.lor.
  Definition ba_consensus_models := ba_binop_models N.land N.lor.
  Definition ba_merge_models     := ba_binop_models N.lor  N.land.

  (** Interleaved constant simulation: requires interleave-indexing lemmas.
    The PArray [parray_interleave] places [even_val] at even indices and
    [odd_val] at odd indices, matching the model's [interleave] on vectors. *)
  Lemma ba_all_true_models : models (all_true n) ba_all_true.
  Proof.
    intro i. unfold ba_all_true, all_true; simpl; unfold Fin_to_int63.
    rewrite (parray_interleave_get _ _ (fin_val i) (fin_lt i)).
    exact (interleave_const_nth (words_per_plane n) (N.ones 64) 0%N i).
  Qed.

  Lemma ba_all_false_models : models (all_false n) ba_all_false.
  Proof.
    intro i. unfold ba_all_false, all_false; simpl; unfold Fin_to_int63.
    rewrite (parray_interleave_get _ _ (fin_val i) (fin_lt i)).
    exact (interleave_const_nth (words_per_plane n) 0%N (N.ones 64) i).
  Qed.

  (** Negation simulation: [parray_swap_aux] swaps even/odd word pairs,
    matching the model's deinterleave-swap-reinterleave in [vec_not]. *)
  Lemma ba_not_models (bv : BVec) (ba : BelnapArr) :
    models bv ba -> models (vec_not bv) (ba_not ba).
  Proof.
    intros Hmod i. unfold ba_not; simpl. unfold Fin_to_int63.
    rewrite vec_not_nth_swap.
    rewrite (Hmod (Fin.of_nat_lt (swap_nat_bound (words_per_plane n)
                                    (fin_val i) (fin_lt i)))).
    unfold Fin_to_int63. rewrite fin_val_of_nat_lt.
    rewrite (parray_swap_get _ (fin_val i) (fin_lt i)).
    unfold swap_nat. destruct (Nat.even (fin_val i)); reflexivity.
  Qed.

End WithBound.
