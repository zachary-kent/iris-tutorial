From stdpp Require Export base list sorting finite.
From iris.heap_lang Require Import array lang proofmode notation par.

(* ################################################################# *)
(** * Case Study: Merge Sort *)

(* ================================================================= *)
(** ** Implementation *)

(**
  Let us implement a simple multithreaded merge sort on arrays. Merge
  sort consists of splitting the array in half until we are left with
  pieces of size [0] or [1]. Then, each pair of pieces is merged into a
  new sorted array.
*)

(**
  We begin by implementing a function which merges two arrays [a₁] and
  [a₂] of lengths [n1] and [n2] into an array [b] of length [n1 + n2].
*)
Definition merge : val :=
  rec: "merge" "a₁" "n1" "a₂" "n2" "b" :=
  (** If [a₁] is empty, we simply copy the second [a₂] into [b]. *)
  if: "n1" = #0 then
    array_copy_to "b" "a₂" "n2"
  (** Likewise if [a₂] is empty instead. *)
  else if: "n2" = #0 then
    array_copy_to "b" "a₁" "n1"
  else
  (**
    Otherwise, we compare the first elements of [a₁] and [a₂]. The
    smallest is removed and written to [b]. Rinse and repeat.
  *)
    let: "x1" := !"a₁" in
    let: "x2" := !"a₂" in
    if: "x1" ≤ "x2" then
      "b" <- "x1";;
      "merge" ("a₁" +ₗ #1) ("n1" - #1) "a₂" "n2" ("b" +ₗ #1)
    else
      "b" <- "x2";;
      "merge" "a₁" "n1" ("a₂" +ₗ #1) ("n2" - #1) ("b" +ₗ #1).

(**
  To sort an array [a], we split the array in half, sort each sub-array
  recursively on separate threads, and merge the sorted sub-arrays using
  [merge], writing the elements back into the array.
*)
Definition merge_sort_inner : val :=
  rec: "merge_sort_inner" "a" "b" "n" :=
  if: "n" ≤ #1 then #()
  else
    let: "n1" := "n" `quot` #2 in
    let: "n2" := "n" - "n1" in
    ("merge_sort_inner" "b" "a" "n1" ||| "merge_sort_inner" ("b" +ₗ "n1") ("a" +ₗ "n1") "n2");;
    merge "b" "n1" ("b" +ₗ "n1") "n2" "a".

(**
  HeapLang requires array allocations to contain at least one element.
  As such, we need to treat this case separately.
*)
Definition merge_sort : val :=
  λ: "a" "n",
  if: "n" = #0 then #()
  else
    let: "b" := AllocN "n" #() in
    array_copy_to "b" "a" "n";;
    merge_sort_inner "a" "b" "n".

(**
  Our desired specification will be that [merge_sort] produces a new
  sorted array which, importantly, is a permutation of the input.
*)

(* ================================================================= *)
(** ** Specifications *)

Section proofs.
Context `{!heapGS Σ, !spawnG Σ}.

Search (Z.of_nat ?x = Z.of_nat ?y → ?x = ?y).

(**
  We begin by giving a specification for the [merge] function. To merge
  two arrays [a₁] and [a₂], we require that they are both already
  sorted. Furthermore, we need the result array [b] to have enough
  space, though we don't care what it contains.
*)

Lemma merge_spec (a₁ a₂ b : loc) (l₁ l₂ : list Z) (l : list val) :
  {{{
    a₁ ↦∗ ((λ x : Z, #x) <$> l₁) ∗
    a₂ ↦∗ ((λ x : Z, #x) <$> l₂) ∗ b ↦∗ l ∗
    ⌜StronglySorted Z.le l₁⌝ ∗
    ⌜StronglySorted Z.le l₂⌝ ∗
    ⌜length l = (length l₁ + length l₂)%nat⌝
  }}}
    merge #a₁ #(length l₁) #a₂ #(length l₂) #b
  {{{(l : list Z), RET #();
    a₁ ↦∗ ((λ x : Z, #x) <$> l₁) ∗
    a₂ ↦∗ ((λ x : Z, #x) <$> l₂) ∗
    b ↦∗ ((λ x : Z, #x) <$> l) ∗
    ⌜StronglySorted Z.le l⌝ ∗
    ⌜l₁ ++ l₂ ≡ₚ l⌝
  }}}.
Proof.
  iIntros "%Φ (Ha₁ & Ha₂ & Hb & %Hsorted₁ & %Hsorted₂ & %Hlen) HΦ".
  iLöb as "IH" forall (a₁ a₂ b l₁ l₂ l Hsorted₁ Hsorted₂ Hlen).
  wp_rec.
  wp_pures.
  case_bool_decide.
  - simplify_eq.
    wp_pures.
    rewrite -Nat2Z.inj_0 in H.
    apply (inj Z.of_nat) in H.
    rewrite H /= in Hlen.
    wp_apply (wp_array_copy_to with "[$Hb $Ha₂]").
    + congruence.
    + by rewrite map_length.
    + iIntros "[Hb Ha₂]".
      iApply "HΦ".
      iFrame.
      iSplit.
      * done.
      * destruct l₁; by simplify_eq.
  - wp_pures.
    case_bool_decide.
    wp_pures.
    rewrite -Nat2Z.inj_0 in H0.
    simplify_eq.
    rewrite H0 /= in Hlen.
    wp_apply (wp_array_copy_to with "[$Hb $Ha₁]").
    + lia.
    + by rewrite map_length.
    + iIntros "[Hb Ha₁]".
      iApply "HΦ".
      iFrame.
      iSplit.
      * done.
      * destruct l₂; last discriminate.
        by rewrite app_nil_r.
    + wp_pures.
      destruct l₁ as [| h₁ t₁]; simplify_eq.
      destruct l₂ as [| h₂ t₂]; simplify_eq.
      clear H H0.
      repeat rewrite fmap_cons.
      iPoseProof (array_cons with "Ha₁") as "[Ha₁ Ha₁']".
      iPoseProof (array_cons with "Ha₂") as "[Ha₂ Ha₂']".
      destruct l; simplify_eq.
      iPoseProof (array_cons with "Hb") as "[Hb Hb']".
      wp_load.
      wp_pures.
      wp_load.
      wp_pures.
      case_bool_decide.
      * wp_pures.
        wp_store.
        wp_pures.
        replace (Z.of_nat (S (length t₁)) - 1)%Z with (Z.of_nat (length t₁)) by lia.
        iApply "IH".
        destruct l; simplify_eq.
        

      iApply array_cons in "Ha₁".
      rewrite /=.
  rewrite /merge.

  (* exercise *)
Admitted.

(**
  With this, we can prove that sort actually sorts the output.
*)
Lemma merge_sort_inner_spec (a b : loc) (l : list Z) :
  {{{
    a ↦∗ ((λ x : Z, #x) <$> l) ∗
    b ↦∗ ((λ x : Z, #x) <$> l)
  }}}
    merge_sort_inner #a #b #(length l)
  {{{(l' : list Z) vs, RET #();
    a ↦∗ ((λ x : Z, #x) <$> l') ∗
    b ↦∗ vs ∗ ⌜StronglySorted Z.le l'⌝ ∗
    ⌜l ≡ₚ l'⌝ ∗
    ⌜length vs = length l'⌝
  }}}.
Proof.
  (* exercise *)
Admitted.

(**
  Finally, we lift this result to the outer [merge_sort] function.
*)
Lemma merge_sort_spec (a : loc) (l : list Z) :
  {{{a ↦∗ ((λ x : Z, #x) <$> l)}}}
    merge_sort #a #(length l)
  {{{(l' : list Z), RET #();
    a ↦∗ ((λ x : Z, #x) <$> l') ∗
    ⌜StronglySorted Z.le l'⌝ ∗
    ⌜l ≡ₚ l'⌝
  }}}.
Proof.
  (* exercise *)
Admitted.

End proofs.
