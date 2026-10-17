import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.Data.Set.Finite.Lattice

/-! An actual closed subset avoiding the generic point of a Noetherian
integral scheme of stalk dimension at most one is finite and consists of
closed points. This is topology of the original scheme, not a support
certificate. SOURCE ONLY / UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry TopologicalSpace
universe u

private theorem integralCurve_nongeneric_isClosed
    (X : Scheme.{u}) [IsIntegral X]
    (hdim : ∀ x : X, Ring.DimensionLEOne (X.presheaf.stalk x))
    (x : X) (hx : x ≠ genericPoint X) : IsClosed ({x} : Set X) := by
  have hbound (y : X) : Order.coheight y ≤ 1 := by
    letI : Ring.DimensionLEOne (X.presheaf.stalk y) := hdim y
    have h := Ring.krullDimLE_iff.mp
      (inferInstance : Ring.KrullDimLE 1 (X.presheaf.stalk y))
    rw [ringKrullDim_stalk_eq_coheight y] at h
    exact_mod_cast h
  have hstrict : x < genericPoint X := by
    change genericPoint X ⤳ x ∧ ¬ x ⤳ genericPoint X
    refine ⟨genericPoint_specializes x, ?_⟩
    intro hxspec
    exact hx (hxspec.antisymm (genericPoint_specializes x)).eq
  have hpos : 0 < Order.coheight x := Order.coheight_pos_of_lt_top hstrict
  apply isClosed_of_closure_subset
  intro y hy
  apply Set.mem_singleton_iff.mpr
  by_contra hne
  have hxy : x ⤳ y := specializes_iff_mem_closure.mpr hy
  have hystrict : y < x := by
    change x ⤳ y ∧ ¬ y ⤳ x
    exact ⟨hxy, fun hyx => hne (hxy.antisymm hyx).eq.symm⟩
  have hfin : Order.coheight x < ⊤ :=
    lt_of_le_of_lt (hbound x) (by simp)
  have hlt : Order.coheight x < 1 :=
    lt_of_lt_of_le (Order.coheight_strictAnti hystrict hfin) (hbound y)
  exact hpos.ne' (Order.lt_one_iff.mp hlt)

/-- A genuine closed set missing the generic point of an actual
Noetherian integral curve is a finite set of actual closed points.
Finite irreducible decomposition is proved by the installed Noetherian
topology API; the stalk-dimension bound forces each component to be a
single closed point. No finite-support or closed-point certificate. -/
theorem integralCurve_closed_avoiding_generic_finite_and_closedPoints
    (X : Scheme.{u}) [IsIntegral X] [NoetherianSpace X]
    (hdim : ∀ x : X, Ring.DimensionLEOne (X.presheaf.stalk x))
    (S : Set X) (hS : IsClosed S) (hg : genericPoint X ∉ S) :
    S.Finite ∧ ∀ x ∈ S, IsClosed ({x} : Set X) := by
  classical
  obtain ⟨F, hF, hFc, hFi, hSF⟩ :=
    NoetherianSpace.exists_finite_set_isClosed_irreducible hS
  have htS (t : Set X) (ht : t ∈ F) : t ⊆ S := by
    rw [hSF]
    exact Set.subset_sUnion_of_mem ht
  have hfinite : S.Finite := by
    rw [hSF]
    apply hF.sUnion
    intro t ht
    let g := (hFi t ht).genericPoint
    have hgmem : g ∈ t := (hFi t ht).isGenericPoint_genericPoint (hFc t ht) |>.mem
    have hgneq : g ≠ genericPoint X := by
      intro h
      exact hg (h ▸ htS t ht hgmem)
    have hgc : IsClosed ({g} : Set X) :=
      integralCurve_nongeneric_isClosed X hdim g hgneq
    have ht : closure ({g} : Set X) = t :=
      (hFi t ht).closure_genericPoint (hFc t ht)
    rw [← ht, hgc.closure_eq]
    exact Set.finite_singleton g
  refine ⟨hfinite, ?_⟩
  intro x hx
  apply integralCurve_nongeneric_isClosed X hdim x
  intro h
  exact hg (h ▸ hx)

end PfaffianDescent.Coray
