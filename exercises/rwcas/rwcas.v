From iris.algebra Require Import excl auth agree frac list cmra csum.
From iris.base_logic.lib Require Export invariants.
From iris.program_logic Require Export atomic.
From iris.proofmode Require Import proofmode.
From iris.heap_lang Require Import proofmode notation.
From iris.prelude Require Import options.

Module Spec.

Record atomic_rwcas {Σ} `{!heapGS Σ} := AtomicRWCAS {
  (* -- operations -- *)
  new_rwcas : val;
  write : val;
  read : val;
  (* -- predicates -- *)
  is_rwcas (N : namespace) (l : loc) : iProp Σ;
  rwcas_state (N : namespace) (l : loc) (n : val) : iProp Σ;
  (* -- predicate properties -- *)
  is_rwcas_persistent N l : Persistent (is_rwcas N l);
  rwcas_state_timeless N l n : Timeless (rwcas_state N l n);
  rwcas_state_exclusive N l n1 n2 :
    rwcas_state N l n1 -∗ rwcas_state N l n2 -∗ False;
  (* -- operation specs -- *)
  new_rwcas_spec N (n : val):
    N ## inv_heapN → inv_heap_inv -∗
    {{{ True }}}
        new_rwcas n
    {{{ l, RET #l ; is_rwcas N l ∗ rwcas_state N l n }}};
  write_spec N (l : loc) (n : val) :
    val_is_unboxed n →
    is_rwcas N l -∗
    <<{ ∀∀ (m : val), rwcas_state N l m }>>
      write #l n @ ↑N ∪ ↑inv_heapN
    <<{ rwcas_state N l n | RET #() }>>;
  read_spec N (l : loc) :
    is_rwcas N l -∗
    <<{ ∀∀ (n : val), rwcas_state N l n }>>
        read #l @ ↑N
    <<{ rwcas_state N l n | RET n }>>;
}.
Global Arguments atomic_rwcas _ {_}.

Global Existing Instances is_rwcas_persistent rwcas_state_timeless.

End Spec.

Import Spec.

Definition new_rwcas : val := λ: "n", ref "n".

Definition read : val := λ: "l", !"l".

Definition write : val := λ: "l" "v", CAS "l" !"l" "v".

(** ** Proof setup *)

Definition valUR      := authR $ optionUR $ exclR valO.
Definition tokenUR    := exclR unitO.
Definition one_shotUR := csumR (exclR unitO) (agreeR unitO).

Class rwcasG Σ := RDCSSG {
                     rwcas_valG      :: inG Σ valUR;
                     rwcas_tokenG    :: inG Σ tokenUR;
                     rwcas_one_shotG :: inG Σ one_shotUR;
                   }.

Definition rwcasΣ : gFunctors :=
  #[GFunctor valUR; GFunctor tokenUR; GFunctor one_shotUR].

Global Instance subG_rwcasΣ {Σ} : subG rwcasΣ Σ → rwcasG Σ.
Proof. solve_inG. Qed.

Section rwcas.
  Context {Σ} `{!heapGS Σ, !rwcasG Σ}.
  Context (N : namespace).

  Implicit Types γ_n γ_a γ_t γ_s : gname.
  Implicit Types l_n l_m l_descr : loc.
  Implicit Types p : proph_id.

  Local Definition descrN := N .@ "descr".
  Local Definition rwcasN := N .@ "rwcas".

  (** Logical value for the N-location. *)

  Definition rwcas_state_auth (l_n : loc) (n : val) :=
    (∃ (γ_n : gname), meta l_n rwcasN γ_n ∗ own γ_n (● Excl' n))%I.

  Definition rwcas_state (l_n : loc) (n : val) :=
    (∃ (γ_n : gname), meta l_n rwcasN γ_n ∗ own γ_n (◯ Excl' n))%I.

  (** Updating and synchronizing the value RAs *)

  Lemma sync_values l_n (n m : val) :
    rwcas_state_auth l_n n -∗ rwcas_state l_n m -∗ ⌜n = m⌝.
  Proof.
    iIntros "H● H◯".
    iDestruct "H●" as (γ) "[#HMeta H●]".
    iDestruct "H◯" as (γ') "[HMeta' H◯]".
    iDestruct (meta_agree with "HMeta' HMeta") as %->. iClear "HMeta'".
    iCombine "H●" "H◯" as "H". iDestruct (own_valid with "H") as "H".
    by iDestruct "H" as %[H%Excl_included%leibniz_equiv _]%auth_both_valid_discrete.
  Qed.

  Lemma update_value l_n (n1 n2 m : val) :
    rwcas_state_auth l_n n1 -∗ rwcas_state l_n n2 ==∗
      rwcas_state_auth l_n m ∗ rwcas_state l_n m.
  Proof.
    iIntros "H● H◯".
    iDestruct "H●" as (γ) "[#HMeta H●]".
    iDestruct "H◯" as (γ') "[HMeta' H◯]".
    iDestruct (meta_agree with "HMeta' HMeta") as %->. iClear "HMeta'".
    iCombine "H●" "H◯" as "H".
    iApply (bupd_mono (meta l_n rwcasN γ ∗ own γ (● Excl' m)
                                         ∗ own γ (◯ Excl' m)))%I.
    { iIntros "(#HMeta & H● & H◯)". iSplitL "H●"; iExists γ; by iFrame. }
    iApply bupd_frame_l. iSplit; first done.
    rewrite -own_op. iApply (own_update with "H").
    by apply auth_update, option_local_update, exclusive_local_update.
  Qed.

  (** Definition of the invariant *)

  (** Extract the [tid] of the winner (i.e., the first thread that preforms a
      CAS) from the prophecy. *)
  Definition proph_extract_winner (pvs : list (val * val)) : option proph_id :=
    match pvs with
    | (_, LitV (LitProphecy tid)) :: _  => Some tid
    | _                                 => None
    end.

  Inductive abstract_state : Set :=
    | Quiescent : val → abstract_state
    | Updating  : loc → loc → val → val → val → proph_id → abstract_state.

  Definition state_to_val (s : abstract_state) : val :=
    match s with
    | Quiescent n                => InjLV n
    | Updating l_descr _ _ _ _ _ => InjRV #l_descr
    end.

  Definition own_token γ := (own γ (Excl ()))%I.

  Definition pending_state P (n1 : val) (proph_winner : option proph_id) tid_ghost_winner l_n γ_a :=
    (P ∗ ⌜from_option (λ p, p = tid_ghost_winner) True proph_winner⌝ ∗
     rwcas_state_auth l_n n1 ∗ own_token γ_a)%I.

  (* After the prophecy said we are going to win the race, we commit and run the AU,
     switching from [pending] to [accepted]. *)
  Definition accepted_state Q (proph_winner : option proph_id) (tid_ghost_winner : proph_id) :=
    ((∃ vs, proph tid_ghost_winner vs) ∗
     Q ∗ ⌜from_option (λ p, p = tid_ghost_winner) True proph_winner⌝)%I.

  (* The same thread then wins the CmpXchg and moves from [accepted] to [done].
     Then, the [γ_t] token guards the transition to take out [Q].
     Remember that the thread winning the CmpXchg might be just helping.  The token
     is owned by the thread whose request this is.
     In this state, [tid_ghost_winner] serves as a token to make sure that
     only the CmpXchg winner can transition to here, and owning half of [l_descr] serves as a
     "location" token to ensure there is no ABA going on. Notice how [rwcas_inv]
     owns *more than* half of its [l_descr] in the Updating state,
     which means we know that the [l_descr] there and here cannot be the same. *)
  Definition done_state Qn l_descr (tid_ghost_winner : proph_id) γ_t γ_a :=
    ((Qn ∨ own_token γ_t) ∗ (∃ vs, proph tid_ghost_winner vs) ∗
     (∃ v, l_descr ↦{# 1/2} v) ∗ own_token γ_a)%I.

  (* Invariant expressing the descriptor protocol.
     - We always need the [proph] in here so that failing threads coming late can
       always resolve their stuff.
     - We need a way for anyone who has observed the [done] state to
       prove that we will always remain [done]; that's what the one-shot token [γ_s] is for.
     - [γ_a] is a token which is owned by the invariant in [pending] and [done] but not in [accepted].
       This permits the CmpXchg winner to gain ownership of the token when moving to [accepted] and
       hence ensures that no other thread can move from [accepted] to [done].
       Side remark: One could get rid of this token if one supported fractional ownership of
                    prophecy resources by only keeping half permission to the prophecy resource
                    in the invariant in [accepted] while the other half would be kept by the CmpXchg winner.
   *)
  Definition descr_inv P Q p n l_n l_descr (tid_ghost_winner : proph_id) γ_t γ_s γ_a: iProp Σ :=
    (∃ vs, proph p vs ∗
      (own γ_s (Cinl $ Excl ()) ∗
       (l_n ↦{# 1/2} InjRV #l_descr ∗ ( pending_state P n (proph_extract_winner vs) tid_ghost_winner l_n γ_a
        ∨ accepted_state (Q n) (proph_extract_winner vs) tid_ghost_winner ))
       ∨ own γ_s (Cinr $ to_agree ()) ∗ done_state (Q n) l_descr tid_ghost_winner γ_t γ_a))%I.

  Local Hint Extern 0 (environments.envs_entails _ (descr_inv _ _ _ _ _ _ _ _ _ _)) => unfold descr_inv : core.

  Definition rwcas_au Q l_n l_m m1 n1 n2 :=
    (AU <{ ∃∃ (m n : val), (l_m ↦_(λ _, True) m) ∗ rwcas_state l_n n }>
         @ ⊤∖(↑N ∪ ↑inv_heapN), ∅
        <{ (l_m ↦_(λ _, True) m) ∗ (rwcas_state l_n (if (decide ((m = m1) ∧ (n = n1))) then n2 else n)),
           COMM Q n }>)%I.

  Definition rwcas_inv l_n :=
    (∃ (s : abstract_state),
       l_n ↦{# 1/2} (state_to_val s) ∗
       match s with
       | Quiescent n =>
           (* (InjLV #n) = state_to_val (Quiescent n) *)
           (* In this state the CmpXchg which expects to read (InjRV _) in
              [complete] fails always.*)
           l_n ↦{# 1/2} (InjLV n) ∗ rwcas_state_auth l_n n
        | Updating l_descr l_m m1 n1 n2 p =>
           ∃ q Q tid_ghost_winner γ_t γ_s γ_a,
             (* (InjRV #l_descr) = state_to_val (Updating l_descr l_m m1 n1 n2 p) *)
             (* There are three pieces of per-[descr]-protocol ghost state:
             - [γ_t] is a token owned by whoever created this protocol and used
               to get out the [Q] in the end.
             - [γ_s] reflects whether the protocol is [done] yet or not.
             - [γ_a] is a token which is used to ensure that only the CmpXchg winner
               can move from the [accepted] to the [done] state. *)
           (* We own *more than* half of [l_descr], which shows that this cannot
              be the [l_descr] of any [descr] protocol in the [done] state. *)
             ⌜val_is_unboxed m1⌝ ∗
             l_descr ↦{# 1/2 + q} (#l_m, m1, n1, n2, #p)%V ∗
             inv descrN (descr_inv (rwcas_au Q l_n l_m m1 n1 n2) Q p n1 l_n l_descr tid_ghost_winner γ_t γ_s γ_a) ∗
             l_m ↦_(λ _, True) □
       end)%I.

  Local Hint Extern 0 (environments.envs_entails _ (rwcas_inv _)) => unfold rwcas_inv : core.

  Definition is_rwcas (l_n : loc) :=
    (inv rwcasN (rwcas_inv l_n) ∧ inv_heap_inv ∧ ⌜N ## inv_heapN⌝)%I.

  Global Instance is_rwcas_persistent l_n : Persistent (is_rwcas l_n) := _.

  Global Instance rwcas_state_timeless l_n n : Timeless (rwcas_state l_n n) := _.

  Global Instance abstract_state_inhabited: Inhabited abstract_state := populate (Quiescent #0).

  Lemma rwcas_state_exclusive l_n n_1 n_2 :
    rwcas_state l_n n_1 -∗ rwcas_state l_n n_2 -∗ False.
  Proof.
    iIntros "Hn1 Hn2".
    iDestruct "Hn1" as (γ_1) "[#Meta1 Hn1]".
    iDestruct "Hn2" as (γ_2) "[#Meta2 Hn2]".
    iDestruct (meta_agree with "Meta1 Meta2") as %->.
    by iCombine "Hn1 Hn2" gives %?%auth_frag_op_valid_1.
  Qed.

  (** A few more helper lemmas that will come up later *)

  (** Once a [descr] protocol is [done] (as reflected by the [γ_s] token here),
      we can at any later point in time extract the [Q]. *)
  Lemma state_done_extract_Q P Q p n l_n l_descr tid_ghost γ_t γ_s γ_a :
    inv descrN (descr_inv P Q p n l_n l_descr tid_ghost γ_t γ_s γ_a) -∗
    own γ_s (Cinr (to_agree ())) -∗
    □(own_token γ_t ={⊤}=∗ ▷ (Q n)).
  Proof.
    iIntros "#Hinv #Hs !# Ht".
    iInv descrN as (vs) "(Hp & [NotDone | Done])".
    * (* Moved back to NotDone: contradiction. *)
      iDestruct "NotDone" as "(>Hs' & _ & _)".
      iCombine "Hs Hs'" gives %?. contradiction.
    * iDestruct "Done" as "(_ & QT & Hrest)".
      iDestruct "QT" as "[Qn | >T]"; last first.
      { iCombine "Ht T" gives %Contra.
          by inversion Contra. }
      iSplitR "Qn"; last done. iIntros "!> !>". unfold descr_inv.
      iExists _. iFrame "Hp". iRight.
      unfold done_state. iFrame "#∗".
  Qed.

  (** ** Proof of [complete] *)

  (** The part of [complete] for the succeeding thread that moves from [accepted] to [done] state *)
  Lemma complete_succeeding_thread_pending γ_t γ_s γ_a l_n P Q p
        (n1 n : val) (l_descr : loc) (tid_ghost : proph_id) Φ :
    inv rwcasN (rwcas_inv l_n) -∗
    inv descrN (descr_inv P Q p n1 l_n l_descr tid_ghost γ_t γ_s γ_a) -∗
    own_token γ_a -∗
    (□(own_token γ_t ={⊤}=∗ ▷ (Q n1)) -∗ Φ #()) -∗
    rwcas_state_auth l_n n -∗
    WP Resolve (CmpXchg #l_n (InjRV #l_descr) (InjLV n)) #p #tid_ghost ;; #() {{ v, Φ v }}.
  Proof.
    iIntros "#InvC #InvS Token_a HQ Hn●". wp_bind (Resolve _ _ _)%E.
    iInv rwcasN as (s) "(>Hln & Hrest)".
    iInv descrN as (vs) "(>Hp & [NotDone | Done])"; last first.
    { (* We cannot be [done] yet, as we own the [γ_a] token that serves
         as token for that transition. *)
      iDestruct "Done" as "(_ & _ & _ & _ & >Token_a')".
      by iCombine "Token_a Token_a'" gives %?.
    }
    iDestruct "NotDone" as "(>Hs & >Hln' & [Pending | Accepted])".
    { (* We also cannot be [Pending] any more because we own the [γ_a] token. *)
      iDestruct "Pending" as "[_ >(_ & _ & Token_a')]".
      by iCombine "Token_a Token_a'" gives %?.
    }
    (* So, we are [Accepted]. Now we can show that (InjRV l_descr) = (state_to_val s), because
       while a [descr] protocol is not [done], it owns enough of
       the [rwcas] protocol to ensure that does not move anywhere else. *)
    destruct s as [n' | l_descr' l_m' m1' n1' n2' p'].
    { simpl. iDestruct (pointsto_agree with "Hln Hln'") as %Heq. inversion Heq. }
    iDestruct (pointsto_agree with "Hln Hln'") as %[= ->].
    simpl.
    iDestruct "Hrest" as (q Q' tid_ghost' γ_t' γ_s' γ_a') "(_ & [>Hld >Hld'] & Hrest)".
    (* We perform the CmpXchg. *)
    iCombine "Hln Hln'" as "Hln".
    wp_apply (wp_resolve with "Hp"); first done. wp_cmpxchg_suc.
    iIntros "!>" (vs'' ->) "Hp'". simpl.
    (* Update to Done. *)
    iDestruct "Accepted" as "[Hp_phost_inv [Q Heq]]".
    iMod (own_update with "Hs") as "Hs".
    { apply (cmra_update_exclusive (Cinr (to_agree ()))). done. }
    iDestruct "Hs" as "#Hs'". iModIntro.
    iSplitL "Hp_phost_inv Token_a Q Hp' Hld".
    (* Update state to Done. *)
    { eauto 12 with iFrame. }
    iModIntro. iSplitR "HQ".
    { iNext. iDestruct "Hln" as "[Hln1 Hln2]". iExists (Quiescent n). by iFrame. }
    wp_seq. iApply "HQ".
    iApply state_done_extract_Q; done.
  Qed.

  (** The part of [complete] for the failing thread *)
  Lemma complete_failing_thread γ_t γ_s γ_a l_n l_descr P Q p n1 n tid_ghost_inv tid_ghost Φ :
    tid_ghost_inv ≠ tid_ghost →
    inv rwcasN (rwcas_inv l_n) -∗
    inv descrN (descr_inv P Q p n1 l_n l_descr tid_ghost_inv γ_t γ_s γ_a) -∗
    (□(own_token γ_t ={⊤}=∗ ▷ (Q n1)) -∗ Φ #()) -∗
    WP Resolve (CmpXchg #l_n (InjRV #l_descr) (InjLV n)) #p #tid_ghost ;; #() {{ v, Φ v }}.
  Proof.
    iIntros (Hnl) "#InvC #InvS HQ". wp_bind (Resolve _ _ _)%E.
    iInv rwcasN as (s) "(>Hln & Hrest)".
    iInv descrN as (vs) "(>Hp & [NotDone | [#Hs Done]])".
    { (* [descr] protocol is not done yet: we can show that it
         is the active protocol still (l = l').  But then the CmpXchg would
         succeed, and our prophecy would have told us that.
         So here we can prove that the prophecy was wrong. *)
        iDestruct "NotDone" as "(_ & >Hln' & State)".
        iDestruct (pointsto_agree with "Hln Hln'") as %[=->].
        iCombine "Hln Hln'" as "Hln".
        wp_apply (wp_resolve with "Hp"); first done; wp_cmpxchg_suc.
        iIntros "!>" (vs'' ->). simpl.
        iDestruct "State" as "[Pending | Accepted]".
        + iDestruct "Pending" as "[_ [%Hvs _]]". by inversion Hvs.
        + iDestruct "Accepted" as "[_ [_ %Hvs]]". by inversion Hvs.
    }
    (* So, we know our protocol is [Done]. *)
    (* It must be that (state_to_val s) ≠ (InjRV l_descr) because we are in the failing thread. *)
    destruct s as [n' | l_descr' l_m' m1' n1' n2' p'].
    - (* (injL n) is the current value, hence the CmpXchg fails *)
      (* FIXME: proof duplication *)
      wp_apply (wp_resolve with "Hp"); first done. wp_cmpxchg_fail.
      iIntros "!>" (vs'' ->) "Hp". iModIntro.
      iSplitL "Done Hp". { by eauto 12 with iFrame. }
      iModIntro.
      iSplitL "Hln Hrest". { by eauto 12 with iFrame. }
      wp_seq. iApply "HQ".
      iApply state_done_extract_Q; done.
    - (* (injR l_descr') is the current value *)
      destruct (decide (l_descr' = l_descr)) as [->|Hn].
      + (* The [descr] protocol is [done] while still being the active protocol
         of the [rwcas] instance?  Impossible, now we will own more than the whole descriptor location! *)
        iDestruct "Done" as "(_ & _ & >Hld & _)".
        iDestruct "Hld" as (v') "Hld".
        iDestruct "Hrest" as (q Q' tid_ghost' γ_t' γ_s' γ_a') "(_ & >[Hld' Hld''] & Hrest)".
        iDestruct (pointsto_combine with "Hld Hld'") as "[Hld _]".
        rewrite dfrac_op_own Qp.half_half.
        by iDestruct (pointsto_ne with "Hld Hld''") as %[].
      + (* l_descr' ≠ l_descr: The CmpXchg fails. *)
        wp_apply (wp_resolve with "Hp"); first done. wp_cmpxchg_fail.
        iIntros "!>" (vs'' ->) "Hp". iModIntro.
        iSplitL "Done Hp". { by eauto 12 with iFrame. }
        iModIntro.
        iSplitL "Hln Hrest". { by eauto 12 with iFrame. }
        wp_seq. iApply "HQ".
        iApply state_done_extract_Q; done.
  Qed.

  (** ** Proof of [complete] *)
  (* The postcondition basically says that *if* you were the thread to own
     this request, then you get [Q].  But we also try to complete other
     thread's requests, which is why we cannot ask for the token
     as a precondition. *)
  Lemma complete_spec l_n l_m l_descr (m1 n1 n2 : val) p γ_t γ_s γ_a tid_ghost_inv Q q :
    val_is_unboxed m1 →
    N ## inv_heapN →
    inv rwcasN (rwcas_inv l_n) -∗
    inv descrN (descr_inv (rwcas_au Q l_n l_m m1 n1 n2) Q p n1 l_n l_descr tid_ghost_inv γ_t γ_s γ_a) -∗
    l_m ↦_(λ _, True) □ -∗
    inv_heap_inv -∗
    {{{ l_descr ↦{q} (#l_m, m1, n1, n2, #p) }}}
       complete #l_descr #l_n
    {{{ RET #(); □ (own_token γ_t ={⊤}=∗ ▷(Q n1)) }}}.
  Proof.
    iIntros (Hm_unbox Hdisj) "#InvC #InvS #isGC #InvGC !>".
    iIntros (Φ) "Hld HQ".  wp_lam. wp_let. wp_bind (! _)%E.
    wp_load. iClear "Hld".
    wp_pure credit:"Hlc". wp_pures.
    wp_apply wp_new_proph; first done.
    iIntros (vs_ghost tid_ghost) "Htid_ghost". wp_pures. wp_bind (! _)%E.
    (* open outer invariant *)
    iInv rwcasN as (s) "(>Hln & Hrest)"=>//.
    (* two different proofs depending on whether we are succeeding thread *)
    destruct (decide (tid_ghost_inv = tid_ghost)) as [-> | Hnl].
    - (* we are the succeeding thread *)
      (* we need to move from [pending] to [accepted]. *)
      iInv descrN as (vs) "(>Hp & [(>Hs & >Hln' & [Pending | Accepted]) | [#Hs Done]])".
      + (* Pending: update to accepted *)
        iDestruct "Pending" as "[AU >(Hvs & Hn● & Token_a)]".
        iMod (lc_fupd_elim_later with "Hlc AU") as "AU".
        iMod (inv_pointsto_own_acc_strong with "InvGC") as "Hgc"; first solve_ndisj.
        (* open and *COMMIT* AU, sync B location l_n and A location l_m *)
        iMod "AU" as (m' n') "[CC [_ Hclose]]".
        iDestruct "CC" as "[Hgc_lm Hn◯]".
        (* sync B location and update it if required *)
        iDestruct (sync_values with "Hn● Hn◯") as %->.
        iMod (update_value _ _ _ (if decide (m' = m1 ∧ n' = n') then n2 else n') with "Hn● Hn◯")
          as "[Hn● Hn◯]".
        (* get access to A location *)
        iDestruct ("Hgc" with "Hgc_lm") as "(_ & Hl & Hgc_close)".
        (* read A location *)
        wp_load.
        (* sync A location *)
        iMod ("Hgc_close" with "[//] Hl") as "[Hgc_lm Hgc_close]".
        (* give back access to A location *)
        iMod ("Hclose" with "[Hn◯ $Hgc_lm]") as "Q"; first done.
        iModIntro. iMod "Hgc_close" as "_".
        (* close descr inv *)
        iModIntro. iSplitL "Q Htid_ghost Hp Hvs Hs Hln'".
        { iModIntro. iNext. iExists _. iFrame "Hp". eauto 12 with iFrame. }
        (* close outer inv *)
        iModIntro. iSplitR "Token_a HQ Hn●".
        { by eauto 12 with iFrame. }
        iModIntro.
        destruct (decide (m' = m1)) as [-> | ?];
        wp_op;
        case_bool_decide; simplify_eq; wp_if; wp_pures;
           [rewrite decide_True; last done | rewrite decide_False; last tauto];
          iApply (complete_succeeding_thread_pending with "InvC InvS Token_a HQ Hn●").
      + (* Accepted: contradiction *)
        iDestruct "Accepted" as "[>Htid_ghost_inv _]".
        iDestruct "Htid_ghost_inv" as (p') "Htid_ghost_inv".
        by iDestruct (proph_exclusive with "Htid_ghost Htid_ghost_inv") as %?.
      + (* Done: contradiction *)
        iDestruct "Done" as "[QT >[Htid_ghost_inv _]]".
        iDestruct "Htid_ghost_inv" as (p') "Htid_ghost_inv".
        by iDestruct (proph_exclusive with "Htid_ghost Htid_ghost_inv") as %?.
    - (* we are the failing thread *)
      (* close invariant *)
      iMod (inv_pointsto_acc with "InvGC isGC") as (v) "(_ & Hlm & Hclose)"; first solve_ndisj.
      wp_load.
      iMod ("Hclose" with "Hlm") as "_". iModIntro.
      iModIntro.
      iSplitL "Hln Hrest".
      { eauto with iFrame. }
      (* two equal proofs depending on value of m1 *)
      wp_op.
      destruct (decide (v = m1)) as [-> | ];
      case_bool_decide; simplify_eq; wp_if;  wp_pures;
      by iApply (complete_failing_thread with "InvC InvS HQ").
  Qed.

  (** ** Proof of [rwcas] *)
  Lemma rwcas_spec (l_n l_m : loc) (m1 n1 n2 : val) :
    val_is_unboxed m1 →
    val_is_unboxed (InjLV n1) →
    is_rwcas l_n -∗
    <<{ ∀∀ (m n: val), l_m ↦_(λ _, True) m ∗ rwcas_state l_n n }>>
        rwcas #l_m #l_n m1 n1 n2 @ ↑N ∪ ↑inv_heapN
    <<{ l_m ↦_(λ _, True) m ∗ rwcas_state l_n (if decide (m = m1 ∧ n = n1) then n2 else n) | RET n }>>.
  Proof.
    iIntros (Hm1_unbox Hn1_unbox) "(#InvR & #InvGC & %)". iIntros (Φ) "AU".
    (* allocate fresh descriptor *)
    wp_lam. wp_pures. wp_apply wp_new_proph; first done.
    iIntros (proph_values p) "Hp".
    wp_let. wp_alloc l_descr as "Hld". wp_pures.
    (* invoke inner recursive function [rwcas_inner] *)
    iLöb as "IH".
    wp_bind (CmpXchg _ _ _)%E.
    (* open outer invariant for the CmpXchg *)
    iInv rwcasN as (s) "(>Hln & Hrest)".
    destruct s as [n | l_descr' l_m' m1' n1' n2' p'].
    - (* l_n ↦ injL n *)
      (* a non-value descriptor n is currently stored at l_n *)
      iDestruct "Hrest" as ">[Hln' Hn●]".
      destruct (decide (n1 = n)) as [-> | Hneq].
      + (* values match -> CmpXchg is successful *)
        iCombine "Hln Hln'" as "Hln".
        wp_cmpxchg_suc.
        (* Take a "peek" at [AU] and abort immediately to get [gc_is_gc f]. *)
        iMod "AU" as (b' n') "[[Hf CC] [Hclose _]]".
        iDestruct (inv_pointsto_own_inv with "Hf") as "#Hgc".
        iMod ("Hclose" with "[Hf CC]") as "AU"; first by iFrame.
        (* Initialize new [descr] protocol .*)
        iMod (own_alloc (Excl ())) as (γ_t) "Token_t"; first done.
        iMod (own_alloc (Excl ())) as (γ_a) "Token_a"; first done.
        iMod (own_alloc (Cinl $ Excl ())) as (γ_s) "Hs"; first done.
        iDestruct "Hln" as "[Hln Hln']".
        set (winner := default p (proph_extract_winner proph_values)).
        iMod (inv_alloc descrN _ (descr_inv _ _ _ _ _ _ winner _ _ _)
              with "[AU Hs Hp Hln' Hn● Token_a]") as "#Hinv".
        { iNext. iExists _. iFrame "Hp". iLeft. iFrame. iLeft.
          iFrame. destruct (proph_extract_winner proph_values); simpl; (iSplit; last done); iExact "AU". }
        iModIntro. iDestruct "Hld" as "[Hld1 [Hld2 Hld3]]". iSplitR "Hld2 Token_t".
        { (* close outer invariant *)
          iNext. iCombine "Hld1 Hld3" as "Hld1".
          iExists (Updating l_descr l_m m1 n n2 p).
          eauto 15 with iFrame. }
        wp_pures.
        wp_apply (complete_spec with "[] [] [] [] [$Hld2]");[ done..|].
        iIntros "Ht". iMod ("Ht" with "Token_t") as "Φ". by wp_seq.
      + (* values do not match -> CmpXchg fails
           we can commit here *)
        wp_cmpxchg_fail.
        iMod "AU" as (m'' n'') "[[Hm◯ Hn◯] [_ Hclose]]"; simpl.
        (* synchronize B location *)
        iDestruct (sync_values with "Hn● Hn◯") as %->.
        iMod ("Hclose" with "[Hm◯ Hn◯]") as "HΦ".
        {  destruct (decide _) as [[_ ?] | _]; [done | iFrame ]. }
        iModIntro. iSplitR "HΦ".
        { iModIntro. iExists (Quiescent n''). iFrame. }
        wp_pures. by iFrame.
    - (* l_n ↦ injR l_ndescr' *)
      (* a descriptor l_descr' is currently stored at l_n -> CmpXchg fails
         try to help the on-going operation *)
      wp_cmpxchg_fail.
      iModIntro.
      (* extract descr invariant *)
      iDestruct "Hrest" as (q Q tid_ghost γ_t γ_s γ_a)
                            "(#Hm1'_unbox & [Hld1 [Hld2 Hld3]] & #InvS & #P_GC)".
      iDestruct "Hm1'_unbox" as %Hm1'_unbox.
      iSplitR "AU Hld2 Hld Hp".
      (* close invariant, retain some permission to l_descr', so it can be read later *)
      { iModIntro. iExists (Updating l_descr' l_m' m1' n1' n2' p'). eauto 15 with iFrame. }
      wp_pures.
      wp_apply (complete_spec with "[] [] [] [] [$Hld2]"); [done..|].
      iIntros "_". wp_seq. wp_pures.
      iApply ("IH" with "AU Hp Hld").
  Qed.

  (** ** Proof of [new_rwcas] *)
  Lemma new_rwcas_spec (n : val) :
    N ## inv_heapN → inv_heap_inv -∗
    {{{ True }}}
        new_rwcas n
    {{{ l_n, RET #l_n ; is_rwcas l_n ∗ rwcas_state l_n n }}}.
  Proof.
    iIntros (Hdisj) "#InvGC". iIntros "!>" (Φ) "_ HΦ".
    wp_lam. wp_pures. iApply wp_fupd. wp_apply wp_alloc; first done.
    iIntros (l_n) "[Hln HMeta]".
    iMod (own_alloc (● Excl' n  ⋅ ◯ Excl' n)) as (γ_n) "[Hn● Hn◯]";
      first by apply auth_both_valid_discrete.
    iMod (meta_set _ l_n γ_n rwcasN with "HMeta") as "#HMeta"; first done.
    iMod (inv_alloc rwcasN _ (rwcas_inv l_n)
      with "[Hln Hn●]") as "#InvR".
    { iDestruct "Hln" as "[Hln1 Hln2]". iExists (Quiescent n).
      iFrame "Hln1 Hln2". iExists γ_n. by iFrame. }
    iModIntro. iApply ("HΦ" $! l_n).
    iSplit; first by iFrame "InvR InvGC".
    iExists γ_n. by iFrame.
  Qed.

  (** ** Proof of [get] *)
  Lemma get_spec l_n :
    is_rwcas l_n -∗
    <<{ ∀∀ (n : val), rwcas_state l_n n }>>
        get #l_n @↑N
    <<{ rwcas_state l_n n | RET n }>>.
  Proof.
    iIntros "(#InvR & #InvGC & %)" (Φ) "AU". iLöb as "IH".
    wp_lam. wp_bind (! _)%E. iInv rwcasN as (s) "(>Hln & Hrest)". wp_load.
    destruct s as [n | l_descr l_m m1 n1 n2 p].
    - iMod "AU" as (au_n) "[Hn◯ [_ Hclose]]".
      iDestruct "Hrest" as "[Hln' Hn●]".
      iDestruct (sync_values with "Hn● Hn◯") as %->.
      iMod ("Hclose" with "Hn◯") as "HΦ".
      iModIntro. iSplitR "HΦ". { iExists (Quiescent au_n). iFrame. }
      wp_match. iApply "HΦ".
    - iDestruct "Hrest" as (q Q tid_ghost γ_t γ_s γ_a)
        "(% & [Hld [Hld' Hld'']] & #InvS & #GC)".
      iModIntro. iSplitR "AU Hld'".
      { iExists (Updating l_descr l_m m1 n1 n2 p). eauto 15 with iFrame. }
      wp_match.
      wp_apply (complete_spec with "[] [] [] [] [$Hld']"); [done..|].
      iIntros "Ht". wp_seq. iApply "IH". iApply "AU".
  Qed.

End rwcas.

Definition atomic_rwcas `{!heapGS Σ, !rwcasG Σ} :
  spec.atomic_rwcas Σ :=
  {| spec.new_rwcas_spec := new_rwcas_spec;
     spec.rwcas_spec := rwcas_spec;
     spec.get_spec := get_spec;
     spec.rwcas_state_exclusive := rwcas_state_exclusive |}.

Global Typeclasses Opaque rwcas_state is_rwcas.
