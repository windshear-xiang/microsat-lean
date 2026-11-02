import MicrosatLean.Verification.Implementation.Propagation.Closure
import MicrosatLean.Verification.Implementation.Representation.Database

namespace MicrosatLean.Verification.Implementation.Initialization

open CDCL Representation Propagation

/-- The source solver initially visits variables in descending order. -/
def initialOrder (n : Nat) : List Nat := (List.range' 1 n).reverse

@[simp] theorem initialOrder_length (n : Nat) : (initialOrder n).length = n := by
  simp [initialOrder]

theorem initialOrder_getD (n i : Nat) : (initialOrder n).getD i 0 = n - i := by
  by_cases within : i < n
  · simp only [initialOrder, List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_getElem (by simpa using within)]
    simp only [Option.getD_some, List.getElem_reverse, List.length_range', List.getElem_range']
    omega
  · have past : (initialOrder n).length ≤ i := by simpa using Nat.le_of_not_gt within
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none past, Nat.sub_eq_zero_of_le
      (Nat.le_of_not_gt within)]

theorem initialOrder_nodup (n : Nat) : (initialOrder n).Nodup := by
  exact (List.reverse_perm _).symm.nodup (List.nodup_range')

theorem initialOrder_mem {var n : Nat} : var ∈ initialOrder n ↔ 1 ≤ var ∧ var ≤ n := by
  simp only [initialOrder, List.mem_reverse, List.mem_range'_1]
  omega

variable (numVars : Nat) (config : Config)

theorem emptyState_arrayBounds : ArrayBounds (emptyState numVars config) := by
  constructor <;> simp [emptyState]

theorem emptyState_arenaBounds : ArenaBounds (emptyState numVars config) := by
  constructor <;> simp [emptyState]

theorem emptyState_database : Database (emptyState numVars config) [] [] := by
  constructor <;> simp [DatabaseFrom, emptyState]

theorem emptyState_trailBounds : TrailBounds (emptyState numVars config) := by
  constructor <;> simp [emptyState]

@[simp] theorem emptyState_mark (lit : Lit) : (emptyState numVars config).mark lit = 0 := by
  simp [emptyState, State.mark, Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?,
    Array.getElem?_replicate]
  split <;> rfl

theorem emptyState_activeTrail : ActiveTrail (emptyState numVars config) := by
  intro i before
  simp [emptyState] at before

theorem emptyState_distinctTrail : DistinctTrailVariables (emptyState numVars config) := by
  intro i j before
  simp [emptyState] at before

theorem emptyState_trailPhases : TrailPhases (emptyState numVars config) := by
  intro i before
  simp [emptyState] at before

theorem emptyState_markedOnTrail : MarkedOnTrail (emptyState numVars config) := by
  intro lit marked
  exact False.elim (marked (emptyState_mark numVars config lit))

theorem emptyState_reasonClauses : ReasonClauses (emptyState numVars config) := by
  intro i before
  simp [emptyState] at before

theorem emptyState_watchList (lit : Lit) : WatchList (emptyState numVars config) lit [] := by
  refine ⟨by simp, ?_, ?_⟩
  · simp [emptyState, Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?,
      Array.getElem?_replicate]
    split <;> rfl
  · intro i before
    simp at before

theorem emptyState_mtfOrder :
    MTFOrder (emptyState numVars config) (initialOrder (max 1 numVars)) := by
  refine ⟨initialOrder_nodup _, ?_, ?_, ?_⟩
  · intro var
    exact initialOrder_mem
  · rw [List.headD_eq_getD, initialOrder_getD]
    simp [emptyState]
  · intro i within
    have within' : i < max 1 numVars := by simpa using within
    simp only [initialOrder_getD]
    constructor
    · simp [emptyState, show max 1 numVars - i < max 1 numVars + 1 by omega]
      omega
    · intro nonhead
      simp [emptyState, show max 1 numVars - i < max 1 numVars + 1 by omega,
        show max 1 numVars - i < max 1 numVars by omega]
      omega

theorem emptyState_mtfCoverage : MTFCoverage (emptyState numVars config) :=
  ⟨_, emptyState_mtfOrder numVars config⟩

end MicrosatLean.Verification.Implementation.Initialization
