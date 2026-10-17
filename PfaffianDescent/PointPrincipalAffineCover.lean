import PfaffianDescent.PointAdaptedCechExt
import PfaffianDescent.SectionRepresenterCechRefinement

/-!
# A point cover with labeled principal-open members

The old adapted cover is retained, and two labeled members for the parameter
principal opens are added. Their indices stay distinct even if their opens
coincide. This permits the standard inverse first lifts to be prescribed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace PfaffianDescent.PointAdaptedAffineCover

universe u

variable {X : Scheme.{u}}

abbrev PrincipalIndex (X : Scheme.{u}) (x : X) := Fin 2 ⊕ Index X x

def principalOpens (U : X.Opens) (x : X) (q f : Γ(X, U)) :
    PrincipalIndex X x → X.Opens
  | Sum.inl k => ![X.basicOpen q, X.basicOpen f] k
  | Sum.inr i => opens U x i

theorem principalOpens_coversTop (U : X.Opens) (x : X) (hx : x ∈ U)
    (hxclosed : IsClosed ({x} : Set X)) (q f : Γ(X, U)) :
    (Opens.grothendieckTopology X).CoversTop (principalOpens U x q f) := by
  apply (Opens.coversTop_iff X _).mpr
  apply top_unique
  intro z hz
  have h : z ∈ ⨆ i, opens U x i := by rw [covers U x hx hxclosed]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp h
  exact (le_iSup (principalOpens U x q f) (Sum.inr i)) hi

theorem principalOpens_isAffineOpen (U : X.Opens) (hU : IsAffineOpen U)
    (x : X) (q f : Γ(X, U)) (i : PrincipalIndex X x) :
    IsAffineOpen (principalOpens U x q f i) := by
  cases i with
  | inl k =>
    fin_cases k
    · exact hU.basicOpen q
    · exact hU.basicOpen f
  | inr i => exact isAffineOpen U hU x i

theorem point_not_mem_basicOpen_of_germ_mem_maximalIdeal
    (U : X.Opens) (x : X) (hx : x ∈ U) (q : Γ(X, U))
    (hq : X.presheaf.germ U x hx q ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x)) :
    x ∉ X.basicOpen q := by
  intro h
  have hu := (X.mem_basicOpen q x hx).mp h
  exact (IsLocalRing.notMem_maximalIdeal.mpr hu) hq

/-- The labeled principal members map to their actual members in the old
adapted cover. The old indices map identically. -/
def principalToAdaptedIndex (U : X.Opens) (hU : IsAffineOpen U)
    (x : X) (hx : x ∈ U) (q f : Γ(X, U))
    (hq : X.presheaf.germ U x hx q ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x))
    (hf : X.presheaf.germ U x hx f ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x)) :
    PrincipalIndex X x → Index X x
  | Sum.inl k => ![
      some ⟨X.basicOpen q, hU.basicOpen q,
        point_not_mem_basicOpen_of_germ_mem_maximalIdeal U x hx q hq⟩,
      some ⟨X.basicOpen f, hU.basicOpen f,
        point_not_mem_basicOpen_of_germ_mem_maximalIdeal U x hx f hf⟩] k
  | Sum.inr i => i

theorem principalToAdaptedIndex_opens (U : X.Opens) (hU : IsAffineOpen U)
    (x : X) (hx : x ∈ U) (q f : Γ(X, U))
    (hq : X.presheaf.germ U x hx q ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x))
    (hf : X.presheaf.germ U x hx f ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x))
    (i : PrincipalIndex X x) :
    opens U x (principalToAdaptedIndex U hU x hx q f hq hf i) =
      principalOpens U x q f i := by
  cases i with
  | inl k => fin_cases k <;> rfl
  | inr i => rfl

/-- The actual chain refinement from the labeled principal cover to the
original adapted cover. -/
def principalToAdaptedChain (U : X.Opens) (hU : IsAffineOpen U)
    (x : X) (hx : x ∈ U) (q f : Γ(X, U))
    (hq : X.presheaf.germ U x hx q ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x))
    (hf : X.presheaf.germ U x hx f ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x)) :
    sectionRepresenterCechChain X.ringCatSheaf (principalOpens U x q f) ⟶
      sectionRepresenterCechChain X.ringCatSheaf (opens U x) :=
  sectionRepresenterCechRefinement X.ringCatSheaf (opens U x) (principalOpens U x q f)
    (principalToAdaptedIndex U hU x hx q f hq hf)
    (fun i => homOfLE (le_of_eq (principalToAdaptedIndex_opens U hU x hx q f hq hf i).symm))

end PfaffianDescent.PointAdaptedAffineCover
