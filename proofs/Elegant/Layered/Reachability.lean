import Std

set_option autoImplicit false

namespace Elegant.Layered.Reachability

abbrev Adjacency := Array (List Nat)

def Bounded (adj : Adjacency) : Prop :=
  ∀ a, a < adj.size → ∀ b ∈ adj[a]!, b < adj.size

def Reach (adj : Adjacency) (source node : Nat) : Prop :=
  source = node ∨ Relation.TransGen (fun a b => b ∈ adj[a]!) source node

structure State where
  seen : Array Bool
  pending : List Nat

def discover (node : Nat) (s : State) : State :=
  if node < s.seen.size then
    if s.seen[node]! then s
    else ⟨s.seen.set! node true, node :: s.pending⟩
  else s

def scan : List Nat → State → State
  | [], s => s
  | node :: rest, s => scan rest (discover node s)

def run (adj : Adjacency) : Nat → State → State
  | 0, s => s
  | fuel + 1, s => match s.pending with
    | [] => s
    | node :: rest => run adj fuel (scan adj[node]! ⟨s.seen, rest⟩)

def search (adj : Adjacency) (source target : Nat) : Bool :=
  let initial := discover source ⟨Array.replicate adj.size false, []⟩
  let fuel := adj.size + adj.foldl (fun total row => total + row.length) 0 + 1
  (run adj fuel initial).seen[target]!

def Marked (s : State) (node : Nat) : Prop := s.seen[node]! = true

def Potential (s : State) : Nat := s.seen.count false + s.pending.length

 theorem reach_step {adj : Adjacency} {source a b : Nat}
    (ha : Reach adj source a) (hab : b ∈ adj[a]!) : Reach adj source b := by
  rcases ha with rfl | ha
  · exact Or.inr (.single hab)
  · exact Or.inr (.tail ha hab)

 theorem discover_size (node : Nat) (s : State) :
    (discover node s).seen.size = s.seen.size := by
  unfold discover
  split
  · split <;> simp
  · rfl

 theorem discover_marked (node : Nat) (s : State) (hi : node < s.seen.size) :
    Marked (discover node s) node := by
  simp only [discover, hi, ↓reduceIte]
  split
  · assumption
  · exact Array.getElem!_set!_self _ _ _ hi

 theorem discover_marks (node : Nat) (s : State) (a : Nat) :
    Marked (discover node s) a ↔ Marked s a ∨ (a = node ∧ node < s.seen.size) := by
  unfold discover Marked
  split
  next hi =>
    split
    next h =>
      constructor
      · exact Or.inl
      · rintro (ha | ⟨rfl, _⟩) <;> assumption
    next h =>
      by_cases he : node = a
      · subst a
        simp [hi]
      · rw [Array.getElem!_set!_ne _ _ _ _ he]
        simp [Ne.symm he]
  next hi =>
    constructor
    · exact Or.inl
    · rintro (ha | ⟨rfl, hb⟩)
      · exact ha
      · exact (hi hb).elim

 theorem discover_pending (node : Nat) (s : State) (a : Nat) :
    a ∈ (discover node s).pending → a ∈ s.pending ∨ a = node := by
  unfold discover
  split
  · split
    · exact Or.inl
    · simp only [List.mem_cons]; intro h; exact h.symm
  · exact Or.inl

 theorem discover_old_pending (node : Nat) (s : State) (a : Nat)
    (ha : a ∈ s.pending) : a ∈ (discover node s).pending := by
  unfold discover
  split
  · split
    · exact ha
    · exact List.mem_cons_of_mem _ ha
  · exact ha

 theorem discover_potential (node : Nat) (s : State) :
    Potential (discover node s) = Potential s := by
  unfold discover
  split
  next hi =>
    split
    · rfl
    next hn =>
      have hf : s.seen[node]! = false := Bool.eq_false_iff.mpr hn
      have hf' : s.seen[node] = false := by rw [← getElem!_pos s.seen node hi]; exact hf
      have hc := Array.boole_getElem_le_count (a := false) hi
      simp only [hf', beq_self_eq_true, ↓reduceIte] at hc
      have he : s.seen.set! node true = s.seen.set node true := by
        simp [Array.set!_eq_setIfInBounds, Array.setIfInBounds, hi]
      have hz : ((true : Bool) == false) = false := rfl
      simp only [Potential, he, Array.count_set hi, hf', beq_self_eq_true,
        hz, Bool.false_eq_true, ↓reduceIte, List.length_cons]
      omega
  · rfl

 theorem scan_size (nodes : List Nat) (s : State) :
    (scan nodes s).seen.size = s.seen.size := by
  induction nodes generalizing s with
  | nil => rfl
  | cons a rest ih => exact (ih _).trans (discover_size _ _)

 theorem scan_potential (nodes : List Nat) (s : State) :
    Potential (scan nodes s) = Potential s := by
  induction nodes generalizing s with
  | nil => rfl
  | cons a rest ih => exact (ih _).trans (discover_potential _ _)

 theorem scan_marks (nodes : List Nat) (s : State) (a : Nat) :
    Marked (scan nodes s) a ↔ Marked s a ∨ (a ∈ nodes ∧ a < s.seen.size) := by
  induction nodes generalizing s with
  | nil => simp [scan]
  | cons node rest ih =>
    simp only [scan, ih, discover_marks, discover_size, List.mem_cons]
    grind

 theorem scan_pending (nodes : List Nat) (s : State) (a : Nat) :
    a ∈ (scan nodes s).pending → a ∈ s.pending ∨ a ∈ nodes := by
  induction nodes generalizing s with
  | nil => exact Or.inl
  | cons node rest ih =>
    intro ha
    rcases ih _ ha with ha | ha
    · rcases discover_pending _ _ _ ha with ha | rfl
      · exact Or.inl ha
      · exact Or.inr (List.mem_cons_self)
    · exact Or.inr (List.mem_cons_of_mem _ ha)

 theorem scan_old_pending (nodes : List Nat) (s : State) (a : Nat)
    (ha : a ∈ s.pending) : a ∈ (scan nodes s).pending := by
  induction nodes generalizing s with
  | nil => exact ha
  | cons node rest ih => exact ih _ (discover_old_pending _ _ _ ha)

 theorem scan_pending_marked (nodes : List Nat) (s : State)
    (hinv : ∀ a ∈ s.pending, Marked s a) :
    ∀ a ∈ (scan nodes s).pending, Marked (scan nodes s) a := by
  induction nodes generalizing s with
  | nil => exact hinv
  | cons node rest ih =>
    apply ih
    intro a ha
    rcases discover_pending _ _ _ ha with ha | rfl
    · exact (discover_marks _ _ _).mpr (Or.inl (hinv _ ha))
    · unfold discover at ha
      split at ha
      next hi => exact discover_marked _ _ hi
      next hi => exact (discover_marks _ _ _).mpr (Or.inl (hinv _ ha))

structure Invariant (adj : Adjacency) (source : Nat) (s : State) : Prop where
  size : s.seen.size = adj.size
  sound : ∀ a, Marked s a → Reach adj source a
  bounded : ∀ a ∈ s.pending, a < adj.size
  pending_marked : ∀ a ∈ s.pending, Marked s a
  start : Marked s source
  frontier : ∀ a, a < adj.size → Marked s a →
    a ∈ s.pending ∨ ∀ b ∈ adj[a]!, Marked s b

 theorem discover_new_pending (node : Nat) (s : State) (a : Nat)
    (ha : Marked (discover node s) a) :
    Marked s a ∨ a ∈ (discover node s).pending := by
  by_cases hi : node < s.seen.size
  · by_cases hm : s.seen[node]! = true
    · rw [discover, ite_eq_left hi, ite_eq_left hm] at ha
      exact Or.inl ha
    · by_cases he : node = a
      · subst a
        rw [discover, ite_eq_left hi, ite_eq_right hm]
        exact Or.inr (by simp)
      · rw [discover, ite_eq_left hi, ite_eq_right hm] at ha
        exact Or.inl (by
          simpa only [Marked, Array.getElem!_set!_ne _ _ _ _ he] using ha)
  · rw [discover, ite_eq_right hi] at ha
    exact Or.inl ha

 theorem scan_new_pending (nodes : List Nat) (s : State) (a : Nat)
    (ha : Marked (scan nodes s) a) :
    Marked s a ∨ a ∈ (scan nodes s).pending := by
  induction nodes generalizing s with
  | nil => exact Or.inl ha
  | cons node rest ih =>
    rcases ih _ ha with hold | hp
    · rcases discover_new_pending _ _ _ hold with hold | hp
      · exact Or.inl hold
      · exact Or.inr (scan_old_pending rest (discover node s) a hp)
    · exact Or.inr hp

 theorem step_invariant (adj : Adjacency) (hAdj : Bounded adj) (source node : Nat)
    (seen : Array Bool) (rest : List Nat)
    (h : Invariant adj source ⟨seen, node :: rest⟩) :
    Invariant adj source (scan adj[node]! ⟨seen, rest⟩) := by
  let s : State := ⟨seen, rest⟩
  have hn : node < adj.size := h.bounded _ (by simp)
  have hr : Reach adj source node := h.sound _ (h.pending_marked _ (by simp))
  have hm (a : Nat) : Marked (scan adj[node]! s) a ↔
      Marked s a ∨ (a ∈ adj[node]! ∧ a < s.seen.size) := scan_marks _ _ _
  refine ⟨(scan_size _ _).trans h.size, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha
    rcases (hm a).mp ha with ha | ⟨ha, _⟩
    · exact h.sound _ ha
    · exact reach_step hr ha
  · intro a ha
    rcases scan_pending _ _ _ ha with ha | ha
    · exact h.bounded _ (by simp [ha])
    · exact hAdj _ hn _ ha
  · apply scan_pending_marked
    intro a ha
    exact h.pending_marked _ (by simp [ha])
  · exact (hm source).mpr (Or.inl h.start)
  · intro a ha hmarked
    by_cases he : a = node
    · subst a
      right
      intro b hb
      exact (hm b).mpr (Or.inr ⟨hb, by simpa [s, h.size] using hAdj _ hn _ hb⟩)
    · rcases scan_new_pending _ _ _ hmarked with hold | hp
      · rcases h.frontier _ ha hold with hp | hc
        · left
          exact scan_old_pending _ _ _ (by simpa [s, he] using hp)
        · right
          intro b hb
          exact (hm b).mpr (Or.inl (hc _ hb))
      · exact Or.inl hp

 theorem run_complete (adj : Adjacency) (hAdj : Bounded adj) (source fuel : Nat)
    (s : State) (hinv : Invariant adj source s) (hf : Potential s ≤ fuel) :
    Invariant adj source (run adj fuel s) ∧ (run adj fuel s).pending = [] := by
  induction fuel generalizing s with
  | zero =>
    have hp : s.pending.length = 0 := by unfold Potential at hf; omega
    exact ⟨hinv, List.length_eq_zero_iff.mp hp⟩
  | succ fuel ih =>
    cases s with
    | mk seen pending =>
      cases pending with
      | nil => exact ⟨hinv, rfl⟩
      | cons node rest =>
        change Invariant adj source (run adj fuel (scan adj[node]! ⟨seen, rest⟩)) ∧ _
        apply ih _ (step_invariant adj hAdj source node seen rest hinv)
        rw [scan_potential]
        unfold Potential at hf ⊢
        simp only [List.length_cons] at hf
        dsimp
        omega

 theorem initial_invariant (adj : Adjacency) (source : Nat) (hs : source < adj.size) :
    Invariant adj source (discover source ⟨Array.replicate adj.size false, []⟩) := by
  let empty : State := ⟨Array.replicate adj.size false, []⟩
  have he (a : Nat) : ¬ Marked empty a := by
    simp only [Marked, empty, Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?,
      Array.getElem?_replicate]
    split <;> simp
  have hm (a : Nat) : Marked (discover source empty) a ↔ a = source := by
    rw [discover_marks]
    simp only [he a, false_or, empty, Array.size_replicate]
    exact and_iff_left hs
  refine ⟨(discover_size _ _).trans (by simp), ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha
    exact Or.inl ((hm a).mp ha).symm
  · intro a ha
    rcases discover_pending _ _ _ ha with ha | rfl
    · simp at ha
    · exact hs
  · intro a ha
    rcases discover_pending _ _ _ ha with ha | rfl
    · simp at ha
    · exact discover_marked _ _ (by simpa [empty] using hs)
  · exact (hm source).mpr rfl
  · intro a _ ha
    have : a = source := (hm a).mp ha
    subst a
    left
    simp [discover, hs]

 theorem reach_bounded (adj : Adjacency) (hAdj : Bounded adj) (source a : Nat)
    (hs : source < adj.size) (hr : Reach adj source a) : a < adj.size := by
  rcases hr with rfl | hr
  · exact hs
  · induction hr with
    | single hab => exact hAdj _ hs _ hab
    | tail _ hab ih => exact hAdj _ ih _ hab

 theorem search_iff (adj : Adjacency) (hAdj : Bounded adj) (source target : Nat)
    (hs : source < adj.size) (_ht : target < adj.size) :
    search adj source target = true ↔ source = target ∨
      Relation.TransGen (fun a b => b ∈ adj[a]!) source target := by
  let initial := discover source ⟨Array.replicate adj.size false, []⟩
  let fuel := adj.size + adj.foldl (fun total row => total + row.length) 0 + 1
  have hp : Potential initial ≤ fuel := by
    rw [show initial = discover source ⟨Array.replicate adj.size false, []⟩ from rfl,
      discover_potential]
    simp only [Potential, Array.count_replicate_self, List.length_nil, Nat.add_zero]
    dsimp [fuel]
    omega
  obtain ⟨hi, hempty⟩ := run_complete adj hAdj source fuel initial
    (initial_invariant adj source hs) hp
  change Marked (run adj fuel initial) target ↔ Reach adj source target
  constructor
  · exact hi.sound target
  · intro hr
    clear _ht
    have closed (a : Nat) (ha : Marked (run adj fuel initial) a)
        (b : Nat) (hab : b ∈ adj[a]!) : Marked (run adj fuel initial) b := by
      have haBound := reach_bounded adj hAdj source a hs (hi.sound a ha)
      rcases hi.frontier a haBound ha with hp | hc
      · simp [hempty] at hp
      · exact hc b hab
    rcases hr with rfl | hr
    · exact hi.start
    · induction hr with
      | single hab => exact closed _ hi.start _ hab
      | tail _ hab ih => exact closed _ ih _ hab

 theorem discover_of_marked (node : Nat) (s : State) (hm : Marked s node) :
    discover node s = s := by
  unfold discover
  split
  · exact ite_eq_left hm
  · rfl

 theorem discover_no_reenqueue (node a : Nat) (s : State)
    (hm : Marked s a) (hp : a ∉ s.pending) :
    a ∉ (discover node s).pending := by
  unfold discover
  split
  · split
    · exact hp
    next hfalse =>
      have hne : a ≠ node := by
        intro he
        subst a
        exact hfalse hm
      simpa only [List.mem_cons, not_or] using And.intro hne hp
  · exact hp

 theorem scan_no_reenqueue (nodes : List Nat) (a : Nat) (s : State)
    (hm : Marked s a) (hp : a ∉ s.pending) :
    a ∉ (scan nodes s).pending := by
  induction nodes generalizing s with
  | nil => exact hp
  | cons node rest ih =>
    exact ih _ ((discover_marks _ _ _).mpr (Or.inl hm))
      (discover_no_reenqueue _ _ _ hm hp)

 theorem discover_nodup (node : Nat) (s : State)
    (hn : s.pending.Nodup) (hm : ∀ a ∈ s.pending, Marked s a) :
    (discover node s).pending.Nodup := by
  unfold discover
  split
  · split
    · exact hn
    next hfalse =>
      apply List.nodup_cons.mpr
      refine ⟨?_, hn⟩
      intro hp
      exact hfalse (hm _ hp)
  · exact hn

 theorem scan_nodup (nodes : List Nat) (s : State)
    (hn : s.pending.Nodup) (hm : ∀ a ∈ s.pending, Marked s a) :
    (scan nodes s).pending.Nodup := by
  induction nodes generalizing s with
  | nil => exact hn
  | cons node rest ih =>
    exact ih _ (discover_nodup _ _ hn hm) (scan_pending_marked [node] s hm)

 inductive PopTrace (adj : Adjacency) : Nat → State → List Nat → Prop where
  | zero (s : State) : PopTrace adj 0 s []
  | empty (fuel : Nat) (seen : Array Bool) :
      PopTrace adj (fuel + 1) ⟨seen, []⟩ []
  | step (fuel node : Nat) (seen : Array Bool) (rest trace : List Nat) :
      PopTrace adj fuel (scan adj[node]! ⟨seen, rest⟩) trace →
      PopTrace adj (fuel + 1) ⟨seen, node :: rest⟩ (node :: trace)

 theorem popTrace_exists (adj : Adjacency) (fuel : Nat) (s : State) :
    ∃ trace, PopTrace adj fuel s trace := by
  induction fuel generalizing s with
  | zero => exact ⟨[], .zero s⟩
  | succ fuel ih =>
    cases s with
    | mk seen pending =>
      cases pending with
      | nil => exact ⟨[], .empty fuel seen⟩
      | cons node rest =>
        obtain ⟨trace, htrace⟩ := ih (scan adj[node]! ⟨seen, rest⟩)
        exact ⟨node :: trace, .step fuel node seen rest trace htrace⟩

 theorem popTrace_excludes_marked_absent {adj : Adjacency} {fuel a : Nat}
    {s : State} {trace : List Nat} (ht : PopTrace adj fuel s trace)
    (hm : Marked s a) (hp : a ∉ s.pending) : a ∉ trace := by
  induction ht with
  | zero => simp
  | empty => simp
  | step fuel node seen rest trace ht ih =>
    have hne : a ≠ node := by intro he; subst a; exact hp (by simp)
    have hr : a ∉ rest := by intro ha; exact hp (by simp [ha])
    have hs : Marked (scan adj[node]! ⟨seen, rest⟩) a :=
      (scan_marks _ _ _).mpr (Or.inl hm)
    intro ha
    rcases List.mem_cons.mp ha with he | ha
    · exact hne he
    · exact ih hs (scan_no_reenqueue _ _ _ hm hr) ha

 theorem popTrace_nodup {adj : Adjacency} {fuel : Nat} {s : State} {trace : List Nat}
    (ht : PopTrace adj fuel s trace) (hn : s.pending.Nodup)
    (hm : ∀ a ∈ s.pending, Marked s a) : trace.Nodup := by
  induction ht with
  | zero => simp
  | empty => simp
  | step fuel node seen rest trace ht ih =>
    obtain ⟨hnot, hrest⟩ := List.nodup_cons.mp hn
    have hmrest : ∀ a ∈ rest, Marked (⟨seen, rest⟩ : State) a :=
      fun a ha => hm a (by simp [ha])
    have hnode : Marked (⟨seen, rest⟩ : State) node := hm node (by simp)
    have hsnode : Marked (scan adj[node]! ⟨seen, rest⟩) node :=
      (scan_marks _ _ _).mpr (Or.inl hnode)
    refine List.nodup_cons.mpr ⟨?_, ?_⟩
    · exact popTrace_excludes_marked_absent ht hsnode
        (scan_no_reenqueue _ _ _ hnode hnot)
    · exact ih (scan_nodup _ _ hrest hmrest) (scan_pending_marked _ _ hmrest)

 theorem search_marks_each_node_once (adj : Adjacency) (source : Nat)
    (trace : List Nat)
    (ht : PopTrace adj
      (adj.size + adj.foldl (fun total row => total + row.length) 0 + 1)
      (discover source ⟨Array.replicate adj.size false, []⟩) trace) :
    trace.Nodup := by
  apply popTrace_nodup ht
  · exact discover_nodup _ _ (by simp) (by simp)
  · exact scan_pending_marked [source] _ (by simp)

end Elegant.Layered.Reachability
