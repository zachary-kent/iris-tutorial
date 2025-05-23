From iris.algebra Require Import auth excl gset numbers.
From iris.base_logic.lib Require Export invariants.
From iris.heap_lang Require Import lang proofmode notation.

(* ################################################################# *)
(** * Case Study: Ticket Lock *)

(* ================================================================= *)
(** ** Implementation *)

(**
  Let us look at another implementation of a lock, namely a ticket lock.
  Instead of having every thread fight to acquire the lock, the ticket
  lock makes them wait in line. It functions similarly to a ticketing
  system that one often finds in bakeries and pharmacies. Upon entering
  the shop, you pick a ticket with some number and wait until the number
  on the screen has reached your number. Once this happens, it becomes
  your turn to speak to the shop assistant. In our scenario, talking to
  the shop assistant corresponds to accessing the protected resources.

  To implement this, we will maintain two counters: [o] and [n]. The
  first counter, [o], represents the number on the screen – the customer
  currently being served. The second counter, [n], represents the next
  number to be dispensed by the ticketing machine.

  To acquire the lock, a thread must increment the second counter, [n],
  and keep its previous value as a ticket for a position in the queue.
  Once the ticket has been obtained, the thread must wait until the
  first counter, [o], reaches its ticket value. Once this happens, the
  thread gets access to the protected resources. The thread can then
  release the lock by incrementing the first counter.
*)

Definition mk_lock : val :=
  λ: <>, (ref #0, ref #0).

Definition wait : val :=
  rec: "wait" "n" "l" :=
  let: "o" := !(Fst "l") in
  if: "o" = "n" then #() else "wait" "n" "l".

Definition acquire : val :=
  rec: "acquire" "l" :=
  let: "n" := !(Snd "l") in
  if: CAS (Snd "l") "n" ("n" + #1) then
    wait "n" "l"
  else
    "acquire" "l".

Definition release : val :=
  λ: "l", Fst "l" <- ! (Fst "l") + #1.

(* ================================================================= *)
(** ** Representation Predicates *)

(**
  As a ticket lock is a lock, we expect it to satisfy the same
  specification as the spin-lock. This time, you have to come up with
  the necessary resource algebra and lock invariant by yourself. It
  might be instructive to first look through all required predicates and
  specifications to figure out exactly what needs to be proven.
*)

Definition RA : cmra := authR (prodUR (optionUR (exclR natO)) (gset_disjR nat)).

Section proofs.
Context `{!heapGS Σ, !inG Σ RA}.

Definition N := nroot .@ "ticket_lock".
(**
  This time around, we know that the thread is locked by a thread with a
  specific ticket. As such, we first define a predicate [locked_by]
  which states that the lock is locked by ticket [o].
*)

Definition locked_by (γ : gname) (o : nat) : iProp Σ := own γ (◯ (Excl' o, GSet ∅)).

(** The lock is locked when it has been locked by some ticket. *)
Definition locked (γ : gname) : iProp Σ :=
  ∃ o, locked_by γ o.

Lemma locked_excl γ : locked γ -∗ locked γ -∗ False.
Proof.
  iIntros "[%o Hγ] [%o' Hγ']".
  rewrite /locked /locked_by.
  iPoseProof (own_valid_2 with "Hγ Hγ'") as "%Hvalid".
  rewrite auth_frag_valid pair_valid in Hvalid.
  destruct Hvalid as [[] _].
Qed.

(**
  We will also have a predicate signifying that ticket [x] has been
  _issued_. A thread will need to have been issued ticket [x] in order
  to wait for the first counter to become [x].
*)
Definition issued (γ : gname) (x : nat) : iProp Σ :=
  own γ (◯ (ε, GSet {[ x ]})).

Definition lock_inv (γ : gname) (lₒ lₙ : loc) (P : iProp Σ) : iProp Σ :=
  ∃ o n : nat, 
    lₒ ↦ #o ∗ 
    lₙ ↦ #n ∗ 
    own γ (● (Excl' o, GSet (set_seq 0 n))) ∗
    ((locked_by γ o ∗ P) ∨ issued γ o).

Definition is_lock (γ : gname) (l : val) (P : iProp Σ) : iProp Σ :=
  ∃ lo ln : loc, ⌜l = (#lo, #ln)%V⌝ ∗ inv N (lock_inv γ lo ln P).

(* ================================================================= *)
(** ** Specifications *)

Lemma mk_lock_spec P :
  {{{ P }}} mk_lock #() {{{ γ l, RET l; is_lock γ l P }}}.
Proof.
  iIntros (Φ) "HP HΦ".
  rewrite /mk_lock.
  wp_pures.
  wp_alloc lₒ as "Hlₒ".
  wp_alloc lₙ as "Hlₙ".
  wp_pures.
  iMod (own_alloc (● (Excl' 0, GSet ∅) ⋅ ◯ (Excl' 0, GSet ∅))) as "(%γ & Hγ & Ho)".
  { by apply auth_both_valid_discrete. }
  iApply "HΦ".
  rewrite /is_lock.
  iExists lₙ, lₒ.
  iSplitR; first done.
  iApply inv_alloc.
  rewrite /lock_inv.
  iExists 0, 0.
  iFrame.
  iLeft.
  iFrame.
Qed.

Lemma wait_spec γ l P x :
  {{{ is_lock γ l P ∗ issued γ x }}}
    wait #x l
  {{{ RET #(); locked γ ∗ P }}}.
Proof.
  iIntros (Φ) "((%lₒ & %lₙ & -> & #Hinv) & Hissued) HΦ".
  iLöb as "IH".
  wp_rec.
  wp_pures.
  wp_bind (! _)%E.
  iInv "Hinv" as "(%o & %n & Hlₒ & Hlₙ & Hγ & Hlock)".
  wp_load.
  destruct (decide (o = x)).
  - subst. iDestruct "Hlock" as "[[Hlock HP] | H]".
    * iFrame.
      iModIntro.
      wp_pures.
      rewrite -> bool_decide_eq_true_2 by done.
      wp_pures.
      iApply "HΦ".
      by iFrame.
    * rewrite /issued.
      iPoseProof (own_valid_2 with "Hissued H") as "%H".
      rewrite auth_frag_valid /= in H.
      rewrite pair_valid /= in H.
      set_solver.
  - iFrame.
    iModIntro.
    wp_pures.
    rewrite -> bool_decide_eq_false_2 by (intros Heq; simplify_eq).
    wp_pures.
    by iApply ("IH" with "Hissued").
Qed.

Lemma acquire_spec γ l P :
  {{{ is_lock γ l P }}} acquire l {{{ RET #(); locked γ ∗ P }}}.
Proof.
  iIntros (Φ) "(%lₒ & %lₙ & -> & #Hinv) HΦ".
  iLöb as "IH".
  wp_rec.
  wp_pures.
  wp_bind (! _)%E.
  iInv "Hinv" as "(%o & %n & Hlₒ & Hlₙ & Hγ & Hlock)".
  wp_load.
  iSplitL "Hlₒ Hlₙ Hγ Hlock".
  { by iFrame. }
  iModIntro.
  wp_pures.
  wp_bind (CmpXchg _ _ _).
  clear o.
  iInv "Hinv" as "(%o & %n' & Hlₒ & Hlₙ & Hγ & Hlock)".
  (* Case on whether ticket was dispensed *)
  destruct (decide (n' = n)).
  + subst.
    wp_cmpxchg_suc.
    replace (Z.of_nat n + 1)%Z with (Z.of_nat (S n)) by lia.
    (* Frame preserving update; add ticket dispensed to waiting queue *)
    iMod (own_update _ _ (● (Excl' o, GSet (set_seq 0 (S n))) ⋅ ◯ (ε, GSet {[n]})) with "Hγ") as "[●Hγ ◯Hγ]".
    { apply auth_update_alloc.
      apply prod_local_update_2.
      rewrite set_seq_S_end_union_L.
      rewrite -gset_disj_union.
      2: { apply set_seq_S_end_disjoint. }
      rewrite -{2}(ucmra_unit_right_id (GSet {[n]})).
      apply gset_disj_alloc_op_local_update.
      apply (set_seq_S_end_disjoint 0). }
      iSplitR "HΦ ◯Hγ".
      - rewrite /lock_inv.
        iExists o, (S n).
        by iFrame.
      - iModIntro.
        wp_pures.
        wp_apply (wait_spec with "[Hinv $◯Hγ]").
        { iExists lₒ, lₙ. by iSplit. }
        iApply "HΦ".
    + wp_cmpxchg_fail.
      { intros Heq. simplify_eq. }
      iSplitR "HΦ".
      * by iFrame.
      * iModIntro.
        wp_pures.
        by wp_apply "IH".
Qed.

Lemma release_spec γ l P :
  {{{ is_lock γ l P ∗ locked γ ∗ P }}} release l {{{ RET #(); True }}}.
Proof.
  iIntros (Φ) "((%lₒ & %lₙ & -> & #Hinv) & [%o Hlocked] & HP) HΦ".
  rewrite /release.
  wp_pures.
  wp_bind (! _)%E.
  iInv "Hinv" as "(%o' & %n & Hlₒ & Hlₙ & ●Hγ & [[>Hlocked' _] | Hissued])".
  {
    iExFalso.
    iApply (locked_excl with "[$Hlocked]").
    iFrame.
  }
  wp_load.
  iSplitL "Hlₒ Hlₙ Hissued ●Hγ".
  { rewrite /lock_inv. iExists o', n. by iFrame. }
  iModIntro.
  wp_pures.
  iInv "Hinv" as "(%o'' & %n' & Hlₒ' & Hlₙ' & ●Hγ' & [[>Hlocked' _] | Hissued'])".
  {
    iExFalso.
    iApply (locked_excl with "[$Hlocked]").
    iFrame.
  }
  wp_store.
  iPoseProof (own_valid_2 with "●Hγ' Hlocked") as "%Hvalid".
  rewrite auth_both_valid_discrete /= in Hvalid.
  rewrite pair_included in Hvalid.
  rewrite Excl_included in Hvalid.
  destruct Hvalid as [[H _] _].
  destruct H.
  iSplitR "HΦ".
  - replace (Z.of_nat o' + 1)%Z with (Z.of_nat (S o')) by lia.
    iCombine "●Hγ' Hlocked" as "Hγ".
   iMod (own_update _ _ (● (Excl' (S o), GSet (set_seq 0 n)) ⋅ ◯ (Excl' (S o), ε)) with "Hγ") as "[Hγ Hexcl]".
   { apply auth_update. }

  - by iApply "HΦ".
  { admit. }
  iNext.
  (* Frame preserving update; remove ticket from waiting queue *)

  rewrite /issued.
  iMod (own_update _ _ (● (Excl' o'', GSet ∅) ⋅ ◯ (Excl' o'', GSet ∅)) with "Hγ") as "[●Hγ ◯Hγ]".
  { }
  iSplitL "Hlₒ Hlₙ Hlocked' Hγ HP".

    iAssert (locked γ) as "Hl". iSplitL "Hlo".
    { rewrite /locked. iExists o. iFrame. }
    iApply locked_excl.
    iApply (locked_excl with "[$o Hlocked] [$o' Hlo]").
   rewrite /locked_by.
   iPoseProof (own_valid_2 with "Hlo Hlocked") as "%H".
   rewrite auth_frag_valid /= in H.
   rewrite pair_valid /= in H.
   destruct H as [[] _].
  }
  

  wp_load.
  iSplitL "Hlₒ Hlₙ".
  + iFrame. admit. 
  (* exercise *)
Admitted.

End proofs.
