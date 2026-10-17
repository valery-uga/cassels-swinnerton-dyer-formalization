import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualIdealCover

/-! # Actual ideal sheaves glue from their literal affine chart pullbacks -/
noncomputable section
open AlgebraicGeometry CategoryTheory
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

theorem serreIncidenceIdeal_comap_injective_of_isIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f]
    {I J : Y.IdealSheafData} (h : I.comap f = J.comap f) : I = J := by
  have h' := congrArg (fun P : X.IdealSheafData => P.comap (inv f)) h
  simpa only [← Scheme.IdealSheafData.comap_comp, IsIso.inv_hom_id,
    Scheme.IdealSheafData.comap_id] using h'

theorem serreIncidenceIdeal_eq_of_affineCover
    {X : Scheme.{u}} (I J : X.IdealSheafData) (C : X.AffineOpenCover)
    (h : ∀ k, I.comap (C.f k) = J.comap (C.f k)) : I = J := by
  let U : C.I₀ → X.affineOpens := fun k =>
    ⟨(C.f k).opensRange, isAffineOpen_opensRange (C.f k)⟩
  have hU : ⨆ k, (U k).1 = ⊤ := by
    apply top_le_iff.mp
    intro x hx
    obtain ⟨y,hy⟩ := C.covers x
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨C.idx x, ⟨y,hy⟩⟩
  apply cubicClosedPointSerreFiniteZeroResidual_ideal_eq_of_affine_pullbacks I J U hU
  intro k
  apply serreIncidenceIdeal_comap_injective_of_isIso (C.f k).isoOpensRange.hom
  change (I.comap (C.f k).opensRange.ι).comap (C.f k).isoOpensRange.hom =
    (J.comap (C.f k).opensRange.ι).comap (C.f k).isoOpensRange.hom
  rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
    Scheme.Hom.isoOpensRange_hom_ι]
  exact h k

end PfaffianDescent
