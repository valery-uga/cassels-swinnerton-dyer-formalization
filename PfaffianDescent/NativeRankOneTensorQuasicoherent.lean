import PfaffianDescent.SchemeModuleLocallyRankOneTensor
import PfaffianDescent.SchemeModuleNativeQuasicoherentKernel
import PfaffianDescent.P3TwistTensorEquivalence

/-! SOURCE ONLY / UNVERIFIED. Native tensoring by an actual locally trivial
rank-one coefficient preserves QC, derived on its actual unit charts.
No tensor-QC/finite-cohomology/duality/RR conclusion is a premise. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
universe u

/-- Actual tensor-over comparison and the actual unit charts preserve QC
on each open. The original scheme modules are retained. -/
theorem schemeModuleTensorRight_isQuasicoherent_of_coversTop_unitCharts
    {X : Scheme.{u}} (M T : X.Modules) [M.IsQuasicoherent]
    {ι : Type u} (B : ι → X.Opens)
    (hB : (Opens.grothendieckTopology X).CoversTop B)
    (eB : ∀ i, T.over (B i) ≅ (SheafOfModules.unit X.ringCatSheaf).over (B i)) :
    (schemeModuleTensor M T).IsQuasicoherent := by
  letI : ∀ i, ((schemeModuleTensor M T).over (B i)).IsQuasicoherent := fun i => by
    let U := B i
    let R := SheafOfModules.commRingSheafOver X.sheaf U
    letI : (M.over U).IsQuasicoherent := SheafOfModules.isQuasicoherent_over M U
    let c : (schemeModuleTensor M T).over U ≅ M.over U :=
      schemeModuleTensorOverIso U M T ≪≫
        SheafOfModules.commRingSheafTensorMapIso R (Iso.refl _) (eB i) ≪≫
        SheafOfModules.commRingSheafTensorUnitRightIso R (M.over U)
    exact (SheafOfModules.isQuasicoherent (X.ringCatSheaf.over U)).prop_of_iso
      c.symm inferInstance
  exact SheafOfModules.IsQuasicoherent.of_coversTop (schemeModuleTensor M T) B hB

/-- Ordinary rank-one geometry chooses the actual unit cover internally. -/
theorem schemeModuleTensorRight_isQuasicoherent_of_locallyRankOne
    {X : Scheme.{u}} (M T : X.Modules) [M.IsQuasicoherent]
    (hT : schemeModuleLocallyRankOne T) : (schemeModuleTensor M T).IsQuasicoherent := by
  classical
  obtain ⟨B, hB, ⟨eB⟩⟩ := schemeModuleLocallyRankOne_pointwise_charts T hT
  have hcover : (Opens.grothendieckTopology X).CoversTop B := by
    apply (Opens.coversTop_iff X B).mpr
    apply top_unique
    intro x hx
    exact Opens.mem_iSup.mpr ⟨x, hB x⟩
  exact schemeModuleTensorRight_isQuasicoherent_of_coversTop_unitCharts M T B hcover eB

open ProjectiveNegativeTwist
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual negative P3 twist supplies its unit charts internally,
including degree zero. This applies in particular to actual presentation
kernels without a new QC assumption on the untwisted kernel. -/
theorem p3ActualNegativeTensor_isQuasicoherent
    (K : Type u) [Field K] (m : ℕ)
    (M : (Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K)).Modules)
    [M.IsQuasicoherent] :
    (schemeModuleTensor M
      (sheafOfModules (MvPolynomial.homogeneousSubmodule (Fin 4) K) m)).IsQuasicoherent := by
  let PS := MvPolynomial.homogeneousSubmodule (Fin 4) K
  let U := p3StandardOpenLifted (K := K)
  exact schemeModuleTensorRight_isQuasicoherent_of_coversTop_unitCharts
    M (sheafOfModules PS m) U (p3StandardOpenLifted_coversTop K)
    (fun j => overFunctorIsoUnit_of_restrictIsoUnit (p3StandardOpen (K := K) j.down)
      (p3NegativeTwistOpenIsoUnit K (p3StandardOpen (K := K) j.down) j.down le_rfl m))

end PfaffianDescent.Coray
