import PfaffianDescent.SchemeModuleGlobalSections
import Mathlib.LinearAlgebra.TensorProduct.Free
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.Flat.Equalizer

/-!
# The canonical finite-basis map on global sections after base change

This file isolates the linear map which the remaining Voisin divisor-class
argument must prove to be an isomorphism.  Mathlib currently has the pullback
functor on module sheaves, but no general theorem that global sections commute
with extension of the ground field.  For a finite-dimensional ground section
space, the map can nevertheless be constructed without any additional
geometric hypothesis: send the chosen finite basis to its literal pullback and
extend linearly, then extend scalars.
-/

namespace PfaffianDescent

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry BundleSectionZeroLocus
open scoped TensorProduct

universe u

noncomputable section

/-- Conjugating both arrows of a linear equalizer by linear equivalences
induces a linear equivalence of their equalizer subspaces. -/
noncomputable def linearEqLocusCongr
    {R N P N' P' : Type u} [Semiring R]
    [AddCommMonoid N] [Module R N]
    [AddCommMonoid P] [Module R P]
    [AddCommMonoid N'] [Module R N']
    [AddCommMonoid P'] [Module R P']
    (d₀ d₁ : N →ₗ[R] P) (d₀' d₁' : N' →ₗ[R] P')
    (eN : N ≃ₗ[R] N') (eP : P ≃ₗ[R] P')
    (h₀ : ∀ x, d₀' (eN x) = eP (d₀ x))
    (h₁ : ∀ x, d₁' (eN x) = eP (d₁ x)) :
    LinearMap.eqLocus d₀ d₁ ≃ₗ[R] LinearMap.eqLocus d₀' d₁' where
  toFun x := ⟨eN x.1, by
    change d₀' (eN x.1) = d₁' (eN x.1)
    rw [h₀, h₁, x.property]⟩
  invFun y := ⟨eN.symm y.1, by
    change d₀ (eN.symm y.1) = d₁ (eN.symm y.1)
    apply eP.injective
    rw [← h₀, ← h₁, eN.apply_symm_apply, y.property]⟩
  left_inv x := by
    ext
    exact eN.symm_apply_apply x.1
  right_inv y := by
    ext
    exact eN.apply_symm_apply y.1
  map_add' x y := by
    ext
    exact eN.map_add x.1 y.1
  map_smul' c x := by
    ext
    exact eN.map_smul c x.1

@[simp]
theorem linearEqLocusCongr_apply
    {R N P N' P' : Type u} [Semiring R]
    [AddCommMonoid N] [Module R N]
    [AddCommMonoid P] [Module R P]
    [AddCommMonoid N'] [Module R N']
    [AddCommMonoid P'] [Module R P']
    (d₀ d₁ : N →ₗ[R] P) (d₀' d₁' : N' →ₗ[R] P')
    (eN : N ≃ₗ[R] N') (eP : P ≃ₗ[R] P')
    (h₀ : ∀ x, d₀' (eN x) = eP (d₀ x))
    (h₁ : ∀ x, d₁' (eN x) = eP (d₁ x))
    (x : LinearMap.eqLocus d₀ d₁) :
    (linearEqLocusCongr d₀ d₁ d₀' d₁' eN eP h₀ h₁ x).1 = eN x.1 :=
  rfl

/-- Scalar extension commutes with a finite product, followed componentwise
by supplied local base-change equivalences. -/
noncomputable def tensorFinitePiLinearEquivOfFamily
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (V : ι → Type u) (W : ι → Type u)
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module L (W i)]
    (e : ∀ i, (L ⊗[K] V i) ≃ₗ[L] W i) :
    (L ⊗[K] (∀ i, V i)) ≃ₗ[L] (∀ i, W i) :=
  TensorProduct.piRight K L L V ≪≫ₗ LinearEquiv.piCongrRight e

@[simp]
theorem tensorFinitePiLinearEquivOfFamily_tmul_apply
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (V : ι → Type u) (W : ι → Type u)
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module L (W i)]
    (e : ∀ i, (L ⊗[K] V i) ≃ₗ[L] W i)
    (c : L) (v : ∀ i, V i) (i : ι) :
    tensorFinitePiLinearEquivOfFamily V W e (c ⊗ₜ[K] v) i =
      e i (c ⊗ₜ[K] v i) := by
  simp [tensorFinitePiLinearEquivOfFamily]

/-- The finite-product tensor equivalence is natural for a family of linear
maps.  This is the componentwise calculation used for both Cech face maps. -/
theorem tensorPiRight_lTensor_pi_apply
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (V W : ι → Type u)
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (f : ∀ i, V i →ₗ[K] W i)
    (x : L ⊗[K] (∀ i, V i)) (i : ι) :
    TensorProduct.piRight K L L W
        (TensorProduct.AlgebraTensorModule.lTensor L L
          (LinearMap.pi (fun j ↦ (f j).comp (LinearMap.proj j))) x) i =
      TensorProduct.AlgebraTensorModule.lTensor L L (f i)
        (TensorProduct.piRight K L L V x i) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul c v => rfl
  | add x y hx hy =>
      rw [(TensorProduct.AlgebraTensorModule.lTensor L L
          (LinearMap.pi (fun j ↦ (f j).comp (LinearMap.proj j)))).map_add,
        (TensorProduct.piRight K L L W).map_add, Pi.add_apply,
        (TensorProduct.piRight K L L V).map_add, Pi.add_apply,
        (TensorProduct.AlgebraTensorModule.lTensor L L (f i)).map_add]
      exact congrArg₂ (fun a b => a + b) hx hy

/-- Naturality when one module maps to every component of a finite product. -/
theorem tensorPiRight_lTensor_pi_apply_sameSource
    {K L V : Type u} [Field K] [Field L] [Algebra K L]
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    [AddCommGroup V] [Module K V]
    (W : ι → Type u) [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (f : ∀ i, V →ₗ[K] W i) (x : L ⊗[K] V) (i : ι) :
    TensorProduct.piRight K L L W
        (TensorProduct.AlgebraTensorModule.lTensor L L (LinearMap.pi f) x) i =
      TensorProduct.AlgebraTensorModule.lTensor L L (f i) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul c v => rfl
  | add x y hx hy =>
      rw [(TensorProduct.AlgebraTensorModule.lTensor L L
          (LinearMap.pi f)).map_add,
        (TensorProduct.piRight K L L W).map_add, Pi.add_apply,
        (TensorProduct.AlgebraTensorModule.lTensor L L (f i)).map_add]
      exact congrArg₂ (fun a b => a + b) hx hy

/-- Two successive finite products can likewise be base changed
componentwise. -/
noncomputable def tensorFinitePiPiLinearEquivOfFamily
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {ι κ : Type u} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    (V : ι → κ → Type u) (W : ι → κ → Type u)
    [∀ i j, AddCommGroup (V i j)] [∀ i j, Module K (V i j)]
    [∀ i j, AddCommGroup (W i j)] [∀ i j, Module L (W i j)]
    (e : ∀ i j, (L ⊗[K] V i j) ≃ₗ[L] W i j) :
    (L ⊗[K] (∀ i j, V i j)) ≃ₗ[L] (∀ i j, W i j) :=
  TensorProduct.piRight K L L (fun i ↦ ∀ j, V i j) ≪≫ₗ
    LinearEquiv.piCongrRight
      (fun i ↦ tensorFinitePiLinearEquivOfFamily (V i) (W i) (e i))

@[simp]
theorem tensorFinitePiPiLinearEquivOfFamily_tmul_apply
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {ι κ : Type u} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    (V : ι → κ → Type u) (W : ι → κ → Type u)
    [∀ i j, AddCommGroup (V i j)] [∀ i j, Module K (V i j)]
    [∀ i j, AddCommGroup (W i j)] [∀ i j, Module L (W i j)]
    (e : ∀ i j, (L ⊗[K] V i j) ≃ₗ[L] W i j)
    (c : L) (v : ∀ i j, V i j) (i : ι) (j : κ) :
    tensorFinitePiPiLinearEquivOfFamily V W e (c ⊗ₜ[K] v) i j =
      e i j (c ⊗ₜ[K] v i j) := by
  simp [tensorFinitePiPiLinearEquivOfFamily]

/-- Naturality of the two-level finite-product equivalence for a family of
maps from each outer component to each corresponding inner component. -/
theorem tensorFinitePiPiLinearEquivOfFamily_lTensor_pi_apply
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {ι κ : Type u} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    (V : ι → Type u) (P : ι → κ → Type u)
    (P' : ι → κ → Type u)
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i j, AddCommGroup (P i j)] [∀ i j, Module K (P i j)]
    [∀ i j, AddCommGroup (P' i j)] [∀ i j, Module L (P' i j)]
    (f : ∀ i j, V i →ₗ[K] P i j)
    (e : ∀ i j, (L ⊗[K] P i j) ≃ₗ[L] P' i j)
    (x : L ⊗[K] (∀ i, V i)) (i : ι) (j : κ) :
    tensorFinitePiPiLinearEquivOfFamily P P' e
        (TensorProduct.AlgebraTensorModule.lTensor L L
          (LinearMap.pi (fun a ↦
            (LinearMap.pi (f a)).comp (LinearMap.proj a))) x) i j =
      e i j
        (TensorProduct.AlgebraTensorModule.lTensor L L (f i j)
          (TensorProduct.piRight K L L V x i)) := by
  change e i j
      (TensorProduct.piRight K L L (P i)
        (TensorProduct.piRight K L L (fun a ↦ ∀ b, P a b)
          (TensorProduct.AlgebraTensorModule.lTensor L L
            (LinearMap.pi (fun a ↦
              (LinearMap.pi (f a)).comp (LinearMap.proj a))) x) i) j) = _
  congr 1
  rw [tensorPiRight_lTensor_pi_apply
    V (fun a ↦ ∀ b, P a b) (fun a ↦ LinearMap.pi (f a)) x i]
  exact tensorPiRight_lTensor_pi_apply_sameSource
    (P i) (fun b ↦ f i b)
    (TensorProduct.piRight K L L V x i) j

/-- Flat base change of two spaces presented as the ground and geometric
kernels of the same linear restriction map.  This is the linear-algebra core
of the finite Cech proof that global sections commute with a field extension. -/
noncomputable def linearEquivBaseChangeOfKernelPresentations
    {K L V N P W : Type u} [Field K] [Field L] [Algebra K L]
    [AddCommGroup V] [Module K V]
    [AddCommGroup N] [Module K N]
    [AddCommGroup P] [Module K P]
    [AddCommGroup W] [Module L W]
    (d : N →ₗ[K] P)
    (ground : V ≃ₗ[K] LinearMap.ker d)
    (geometric : LinearMap.ker
      (TensorProduct.AlgebraTensorModule.lTensor L L d) ≃ₗ[L] W) :
    (L ⊗[K] V) ≃ₗ[L] W :=
  ground.baseChange K L V (LinearMap.ker d) ≪≫ₗ
    LinearMap.tensorKerEquiv L L d ≪≫ₗ geometric

/-- On a scalar-extended vector, the kernel-presentation equivalence is the
canonical flat tensor-kernel map followed by the supplied geometric
presentation. -/
theorem linearEquivBaseChangeOfKernelPresentations_apply
    {K L V N P W : Type u} [Field K] [Field L] [Algebra K L]
    [AddCommGroup V] [Module K V]
    [AddCommGroup N] [Module K N]
    [AddCommGroup P] [Module K P]
    [AddCommGroup W] [Module L W]
    (d : N →ₗ[K] P)
    (ground : V ≃ₗ[K] LinearMap.ker d)
    (geometric : LinearMap.ker
      (TensorProduct.AlgebraTensorModule.lTensor L L d) ≃ₗ[L] W)
    (v : L ⊗[K] V) :
    linearEquivBaseChangeOfKernelPresentations d ground geometric v =
      geometric (LinearMap.tensorKerEquiv L L d
        (ground.baseChange K L V (LinearMap.ker d) v)) := rfl

/-- Equalizer version of `linearEquivBaseChangeOfKernelPresentations`, in the
form directly produced by the sheaf condition for a finite affine cover. -/
noncomputable def linearEquivBaseChangeOfEqLocusPresentations
    {K L V N P W : Type u} [Field K] [Field L] [Algebra K L]
    [AddCommGroup V] [Module K V]
    [AddCommGroup N] [Module K N]
    [AddCommGroup P] [Module K P]
    [AddCommGroup W] [Module L W]
    (d₀ d₁ : N →ₗ[K] P)
    (ground : V ≃ₗ[K] LinearMap.eqLocus d₀ d₁)
    (geometric : LinearMap.eqLocus
      (TensorProduct.AlgebraTensorModule.lTensor L L d₀)
      (TensorProduct.AlgebraTensorModule.lTensor L L d₁) ≃ₗ[L] W) :
    (L ⊗[K] V) ≃ₗ[L] W :=
  ground.baseChange K L V (LinearMap.eqLocus d₀ d₁) ≪≫ₗ
    LinearMap.tensorEqLocusEquiv L L d₀ d₁ ≪≫ₗ geometric

theorem linearEquivBaseChangeOfEqLocusPresentations_apply
    {K L V N P W : Type u} [Field K] [Field L] [Algebra K L]
    [AddCommGroup V] [Module K V]
    [AddCommGroup N] [Module K N]
    [AddCommGroup P] [Module K P]
    [AddCommGroup W] [Module L W]
    (d₀ d₁ : N →ₗ[K] P)
    (ground : V ≃ₗ[K] LinearMap.eqLocus d₀ d₁)
    (geometric : LinearMap.eqLocus
      (TensorProduct.AlgebraTensorModule.lTensor L L d₀)
      (TensorProduct.AlgebraTensorModule.lTensor L L d₁) ≃ₗ[L] W)
    (v : L ⊗[K] V) :
    linearEquivBaseChangeOfEqLocusPresentations d₀ d₁ ground geometric v =
      geometric (LinearMap.tensorEqLocusEquiv L L d₀ d₁
        (ground.baseChange K L V (LinearMap.eqLocus d₀ d₁) v)) := rfl

/-- Cech assembly of global-section base change.  It is enough to identify
the scalar extensions of the products of local sections and overlap
sections with their geometric counterparts, compatibly with both face maps. -/
noncomputable def linearEquivBaseChangeOfCechPresentations
    {K L V N P N' P' W : Type u} [Field K] [Field L] [Algebra K L]
    [AddCommGroup V] [Module K V]
    [AddCommGroup N] [Module K N]
    [AddCommGroup P] [Module K P]
    [AddCommGroup N'] [Module L N']
    [AddCommGroup P'] [Module L P']
    [AddCommGroup W] [Module L W]
    (d₀ d₁ : N →ₗ[K] P) (d₀' d₁' : N' →ₗ[L] P')
    (ground : V ≃ₗ[K] LinearMap.eqLocus d₀ d₁)
    (localEquiv : (L ⊗[K] N) ≃ₗ[L] N')
    (overlap : (L ⊗[K] P) ≃ₗ[L] P')
    (h₀ : ∀ x,
      d₀' (localEquiv x) = overlap
        (TensorProduct.AlgebraTensorModule.lTensor L L d₀ x))
    (h₁ : ∀ x,
      d₁' (localEquiv x) = overlap
        (TensorProduct.AlgebraTensorModule.lTensor L L d₁ x))
    (geometric : LinearMap.eqLocus d₀' d₁' ≃ₗ[L] W) :
    (L ⊗[K] V) ≃ₗ[L] W :=
  ground.baseChange K L V (LinearMap.eqLocus d₀ d₁) ≪≫ₗ
    LinearMap.tensorEqLocusEquiv L L d₀ d₁ ≪≫ₗ
      linearEqLocusCongr
        (TensorProduct.AlgebraTensorModule.lTensor L L d₀)
        (TensorProduct.AlgebraTensorModule.lTensor L L d₁)
        d₀' d₁' localEquiv overlap h₀ h₁ ≪≫ₗ
          geometric

/-- On a pure tensor, the Cech base-change equivalence is obtained by
extending each local coordinate and then gluing. This formula is what must
be compared with literal pullback of a global section on the chosen basis. -/
theorem linearEquivBaseChangeOfCechPresentations_tmul_apply
    {K L V N P N' P' W : Type u} [Field K] [Field L] [Algebra K L]
    [AddCommGroup V] [Module K V]
    [AddCommGroup N] [Module K N]
    [AddCommGroup P] [Module K P]
    [AddCommGroup N'] [Module L N']
    [AddCommGroup P'] [Module L P']
    [AddCommGroup W] [Module L W]
    (d₀ d₁ : N →ₗ[K] P) (d₀' d₁' : N' →ₗ[L] P')
    (ground : V ≃ₗ[K] LinearMap.eqLocus d₀ d₁)
    (localEquiv : (L ⊗[K] N) ≃ₗ[L] N')
    (overlap : (L ⊗[K] P) ≃ₗ[L] P')
    (h₀ : ∀ x,
      d₀' (localEquiv x) = overlap
        (TensorProduct.AlgebraTensorModule.lTensor L L d₀ x))
    (h₁ : ∀ x,
      d₁' (localEquiv x) = overlap
        (TensorProduct.AlgebraTensorModule.lTensor L L d₁ x))
    (geometric : LinearMap.eqLocus d₀' d₁' ≃ₗ[L] W)
    (l : L) (v : V) :
    geometric.symm
      (linearEquivBaseChangeOfCechPresentations
        d₀ d₁ d₀' d₁' ground localEquiv overlap h₀ h₁ geometric
          (l ⊗ₜ[K] v)) =
      ⟨localEquiv (l ⊗ₜ[K] (ground v).1), by
        change d₀' (localEquiv (l ⊗ₜ[K] (ground v).1)) =
          d₁' (localEquiv (l ⊗ₜ[K] (ground v).1))
        rw [h₀, h₁]
        change overlap (l ⊗ₜ[K] d₀ (ground v).1) =
          overlap (l ⊗ₜ[K] d₁ (ground v).1)
        rw [(ground v).property]⟩ := by
  apply Subtype.ext
  simp only [linearEquivBaseChangeOfCechPresentations,
    LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply,
    LinearEquiv.baseChange_tmul, LinearMap.tensorEqLocusEquiv_apply,
    LinearMap.tensorEqLocus_tmul, linearEqLocusCongr_apply]

/-- Extension of a scheme over `K` to a field extension `L/K`. -/
noncomputable abbrev schemeFieldBaseChange
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} (base : X ⟶ Spec (.of K)) : Scheme.{u} :=
  pullback base (Spec.map (CommRingCat.ofHom (algebraMap K L)))

/-- Projection from the field base change back to the original scheme. -/
noncomputable def schemeFieldBaseChangeToOriginal
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} (base : X ⟶ Spec (.of K)) :
    schemeFieldBaseChange (L := L) base ⟶ X :=
  pullback.fst base (Spec.map (CommRingCat.ofHom (algebraMap K L)))

/-- Structure map of the field base change to `Spec L`. -/
noncomputable def schemeFieldBaseChangeToField
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} (base : X ⟶ Spec (.of K)) :
    schemeFieldBaseChange (L := L) base ⟶ Spec (.of L) :=
  pullback.snd base (Spec.map (CommRingCat.ofHom (algebraMap K L)))

theorem schemeFieldBaseChange_condition
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} (base : X ⟶ Spec (.of K)) :
    schemeFieldBaseChangeToOriginal (L := L) base ≫ base =
      schemeFieldBaseChangeToField (L := L) base ≫
        Spec.map (CommRingCat.ofHom (algebraMap K L)) :=
  pullback.condition

/-- A field-valued point over the scalar-extension map has its canonical lift
to the field base change. -/
noncomputable def schemeFieldBaseChangePoint
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} (base : X ⟶ Spec (.of K))
    (x : Spec (.of L) ⟶ X)
    (hx : x ≫ base = Spec.map (CommRingCat.ofHom (algebraMap K L))) :
    Spec (.of L) ⟶ schemeFieldBaseChange (L := L) base :=
  pullback.lift x (𝟙 _) (by simpa using hx)

@[reassoc]
theorem schemeFieldBaseChangePoint_toOriginal
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} (base : X ⟶ Spec (.of K))
    (x : Spec (.of L) ⟶ X)
    (hx : x ≫ base = Spec.map (CommRingCat.ofHom (algebraMap K L))) :
    schemeFieldBaseChangePoint base x hx ≫
      schemeFieldBaseChangeToOriginal (L := L) base = x :=
  pullback.lift_fst _ _ _

@[reassoc]
theorem schemeFieldBaseChangePoint_toField
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} (base : X ⟶ Spec (.of K))
    (x : Spec (.of L) ⟶ X)
    (hx : x ≫ base = Spec.map (CommRingCat.ofHom (algebraMap K L))) :
    schemeFieldBaseChangePoint base x hx ≫
      schemeFieldBaseChangeToField (L := L) base = 𝟙 _ :=
  pullback.lift_snd _ _ _

/-- The `K`-linear map from ground global sections to global sections of the
pulled-back module, characterized on `Module.finBasis` by literal pullback of
sections.  Defining it by the finite basis avoids hiding scalar-pullback
naturality inside an assumed map. -/
noncomputable def schemeModuleGlobalSectionsPullbackLinearMapOfFinBasis
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X Y : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (baseL : Y ⟶ Spec (.of L))
    (f : Y ⟶ X) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)] :
    SchemeModuleGlobalSectionsOver base M →ₗ[K]
      RestrictScalars K L
        (SchemeModuleGlobalSectionsOver baseL
          ((Scheme.Modules.pullback f).obj M)) :=
  (Module.finBasis K (SchemeModuleGlobalSectionsOver base M)).constr K
    (fun i =>
      (RestrictScalars.addEquiv K L _).symm
        ((schemeModuleGlobalSectionsOverEquivSections baseL
          ((Scheme.Modules.pullback f).obj M)).symm
            (BundleSectionZeroLocus.pullbackSection f M
              (BundleSectionZeroLocus.isIso_pullbackUnitComparison f)
              (schemeModuleGlobalSectionsOverEquivSections base M
                (Module.finBasis K
                  (SchemeModuleGlobalSectionsOver base M) i)))))

@[simp]
theorem schemeModuleGlobalSectionsPullbackLinearMapOfFinBasis_finBasis
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X Y : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (baseL : Y ⟶ Spec (.of L))
    (f : Y ⟶ X) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    (i : Fin (Module.finrank K (SchemeModuleGlobalSectionsOver base M))) :
    schemeModuleGlobalSectionsPullbackLinearMapOfFinBasis base baseL f M
        (Module.finBasis K (SchemeModuleGlobalSectionsOver base M) i) =
      (RestrictScalars.addEquiv K L _).symm
        ((schemeModuleGlobalSectionsOverEquivSections baseL
          ((Scheme.Modules.pullback f).obj M)).symm
            (BundleSectionZeroLocus.pullbackSection f M
              (BundleSectionZeroLocus.isIso_pullbackUnitComparison f)
              (schemeModuleGlobalSectionsOverEquivSections base M
                (Module.finBasis K
                  (SchemeModuleGlobalSectionsOver base M) i)))) := by
  exact (Module.finBasis K
    (SchemeModuleGlobalSectionsOver base M)).constr_basis K _ i

/-- The actual scalar-extension map on global sections obtained from the
literal pullbacks of the finite ground basis. -/
noncomputable def schemeModuleGlobalSectionsBaseChangeLinearMapOfFinBasis
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X Y : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (baseL : Y ⟶ Spec (.of L))
    (f : Y ⟶ X) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)] :
    (L ⊗[K] SchemeModuleGlobalSectionsOver base M) →ₗ[L]
      SchemeModuleGlobalSectionsOver baseL
        ((Scheme.Modules.pullback f).obj M) :=
  by
    let W := SchemeModuleGlobalSectionsOver baseL
      ((Scheme.Modules.pullback f).obj M)
    letI : Module K W := Module.restrictScalars K L W
    letI : IsScalarTower K L W := IsScalarTower.restrictScalars K L W
    let unwrap : RestrictScalars K L W →ₗ[K] W :=
      { toFun := RestrictScalars.addEquiv K L W
        map_add' := (RestrictScalars.addEquiv K L W).map_add
        map_smul' := fun _ _ => rfl }
    let g : SchemeModuleGlobalSectionsOver base M →ₗ[K] W :=
      unwrap.comp
        (schemeModuleGlobalSectionsPullbackLinearMapOfFinBasis base baseL f M)
    exact LinearMap.liftBaseChange L g

@[simp]
theorem schemeModuleGlobalSectionsBaseChangeLinearMapOfFinBasis_one_tmul_finBasis
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X Y : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (baseL : Y ⟶ Spec (.of L))
    (f : Y ⟶ X) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    (i : Fin (Module.finrank K (SchemeModuleGlobalSectionsOver base M))) :
    schemeModuleGlobalSectionsBaseChangeLinearMapOfFinBasis base baseL f M
        (1 ⊗ₜ[K] Module.finBasis K
          (SchemeModuleGlobalSectionsOver base M) i) =
      (schemeModuleGlobalSectionsOverEquivSections baseL
        ((Scheme.Modules.pullback f).obj M)).symm
          (BundleSectionZeroLocus.pullbackSection f M
            (BundleSectionZeroLocus.isIso_pullbackUnitComparison f)
            (schemeModuleGlobalSectionsOverEquivSections base M
              (Module.finBasis K
                (SchemeModuleGlobalSectionsOver base M) i))) := by
  unfold schemeModuleGlobalSectionsBaseChangeLinearMapOfFinBasis
  dsimp only
  rw [LinearMap.liftBaseChange_one_tmul]
  change RestrictScalars.addEquiv K L _
      (schemeModuleGlobalSectionsPullbackLinearMapOfFinBasis base baseL f M
        (Module.finBasis K (SchemeModuleGlobalSectionsOver base M) i)) = _
  rw [schemeModuleGlobalSectionsPullbackLinearMapOfFinBasis_finBasis]
  exact (RestrictScalars.addEquiv K L _).apply_symm_apply _

/-- Once the geometric argument proves bijectivity, the canonical map above
is exactly the linear equivalence consumed by the final descent endpoint. -/
noncomputable def schemeModuleGlobalSectionsBaseChangeLinearEquivOfFinBasis
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X Y : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (baseL : Y ⟶ Spec (.of L))
    (f : Y ⟶ X) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    (h : Function.Bijective
      (schemeModuleGlobalSectionsBaseChangeLinearMapOfFinBasis
        base baseL f M)) :
    (L ⊗[K] SchemeModuleGlobalSectionsOver base M) ≃ₗ[L]
      SchemeModuleGlobalSectionsOver baseL
        ((Scheme.Modules.pullback f).obj M) :=
  LinearEquiv.ofBijective
    (schemeModuleGlobalSectionsBaseChangeLinearMapOfFinBasis base baseL f M) h

@[simp]
theorem schemeModuleGlobalSectionsBaseChangeLinearEquivOfFinBasis_apply
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X Y : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (baseL : Y ⟶ Spec (.of L))
    (f : Y ⟶ X) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    (h : Function.Bijective
      (schemeModuleGlobalSectionsBaseChangeLinearMapOfFinBasis
        base baseL f M))
    (v : L ⊗[K] SchemeModuleGlobalSectionsOver base M) :
    schemeModuleGlobalSectionsBaseChangeLinearEquivOfFinBasis
        base baseL f M h v =
      schemeModuleGlobalSectionsBaseChangeLinearMapOfFinBasis
        base baseL f M v := rfl

/-- A geometric base-change equivalence identifies the *canonical* pullback
map as soon as it sends each scalar-extended ground basis section to its
literal pullback. This is the final comparison needed when a Cech argument
constructs the equivalence through local presentations. -/
theorem schemeModuleGlobalSectionsBaseChangeLinearMapOfFinBasis_bijective_of_equiv_basis
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X Y : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (baseL : Y ⟶ Spec (.of L))
    (f : Y ⟶ X) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    (e : (L ⊗[K] SchemeModuleGlobalSectionsOver base M) ≃ₗ[L]
      SchemeModuleGlobalSectionsOver baseL
        ((Scheme.Modules.pullback f).obj M))
    (hbasis : ∀ i : Fin (Module.finrank K
        (SchemeModuleGlobalSectionsOver base M)),
      e (1 ⊗ₜ[K] Module.finBasis K
        (SchemeModuleGlobalSectionsOver base M) i) =
        (schemeModuleGlobalSectionsOverEquivSections baseL
          ((Scheme.Modules.pullback f).obj M)).symm
            (BundleSectionZeroLocus.pullbackSection f M
              (BundleSectionZeroLocus.isIso_pullbackUnitComparison f)
              (schemeModuleGlobalSectionsOverEquivSections base M
                (Module.finBasis K
                  (SchemeModuleGlobalSectionsOver base M) i)))) :
    Function.Bijective
      (schemeModuleGlobalSectionsBaseChangeLinearMapOfFinBasis
        base baseL f M) := by
  have heq : schemeModuleGlobalSectionsBaseChangeLinearMapOfFinBasis
      base baseL f M = e.toLinearMap := by
    apply (Module.finBasis K
      (SchemeModuleGlobalSectionsOver base M)).baseChange L |>.ext
    intro i
    rw [Module.Basis.baseChange_apply]
    change schemeModuleGlobalSectionsBaseChangeLinearMapOfFinBasis
        base baseL f M (1 ⊗ₜ[K] Module.finBasis K
          (SchemeModuleGlobalSectionsOver base M) i) =
      e (1 ⊗ₜ[K] Module.finBasis K
        (SchemeModuleGlobalSectionsOver base M) i)
    rw [schemeModuleGlobalSectionsBaseChangeLinearMapOfFinBasis_one_tmul_finBasis]
    exact (hbasis i).symm
  rw [heq]
  exact e.bijective

/-- A finite Cech presentation proves bijectivity of the literal
global-sections pullback map once the local coordinates of each pulled-back
ground basis section agree with the componentwise scalar extension. -/
theorem schemeModuleGlobalSectionsBaseChangeLinearMapOfFinBasis_bijective_of_Cech
    {K L N P N' P' : Type u} [Field K] [Field L] [Algebra K L]
    [AddCommGroup N] [Module K N]
    [AddCommGroup P] [Module K P]
    [AddCommGroup N'] [Module L N']
    [AddCommGroup P'] [Module L P']
    {X Y : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (baseL : Y ⟶ Spec (.of L))
    (f : Y ⟶ X) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    (d₀ d₁ : N →ₗ[K] P) (d₀' d₁' : N' →ₗ[L] P')
    (ground : SchemeModuleGlobalSectionsOver base M ≃ₗ[K]
      LinearMap.eqLocus d₀ d₁)
    (localEquiv : (L ⊗[K] N) ≃ₗ[L] N')
    (overlap : (L ⊗[K] P) ≃ₗ[L] P')
    (h₀ : ∀ x,
      d₀' (localEquiv x) = overlap
        (TensorProduct.AlgebraTensorModule.lTensor L L d₀ x))
    (h₁ : ∀ x,
      d₁' (localEquiv x) = overlap
        (TensorProduct.AlgebraTensorModule.lTensor L L d₁ x))
    (geometric : LinearMap.eqLocus d₀' d₁' ≃ₗ[L]
      SchemeModuleGlobalSectionsOver baseL
        ((Scheme.Modules.pullback f).obj M))
    (hbasis : ∀ i : Fin (Module.finrank K
        (SchemeModuleGlobalSectionsOver base M)),
      (geometric.symm
        ((schemeModuleGlobalSectionsOverEquivSections baseL
          ((Scheme.Modules.pullback f).obj M)).symm
            (BundleSectionZeroLocus.pullbackSection f M
              (BundleSectionZeroLocus.isIso_pullbackUnitComparison f)
              (schemeModuleGlobalSectionsOverEquivSections base M
                (Module.finBasis K
                  (SchemeModuleGlobalSectionsOver base M) i))))).1 =
        localEquiv (1 ⊗ₜ[K]
          (ground (Module.finBasis K
            (SchemeModuleGlobalSectionsOver base M) i)).1)) :
    Function.Bijective
      (schemeModuleGlobalSectionsBaseChangeLinearMapOfFinBasis
        base baseL f M) := by
  let e := linearEquivBaseChangeOfCechPresentations
    d₀ d₁ d₀' d₁' ground localEquiv overlap h₀ h₁ geometric
  apply schemeModuleGlobalSectionsBaseChangeLinearMapOfFinBasis_bijective_of_equiv_basis
    base baseL f M e
  intro i
  apply geometric.symm.injective
  apply Subtype.ext
  have hcech := congrArg Subtype.val
    (linearEquivBaseChangeOfCechPresentations_tmul_apply
      d₀ d₁ d₀' d₁' ground localEquiv overlap h₀ h₁ geometric
        1 (Module.finBasis K (SchemeModuleGlobalSectionsOver base M) i))
  exact hcech.trans (hbasis i).symm

/-- Canonical global-sections map for the actual field base change
`X ×_{Spec K} Spec L`. -/
noncomputable def schemeModuleGlobalSectionsFieldBaseChangeLinearMap
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)] :
    (L ⊗[K] SchemeModuleGlobalSectionsOver base M) →ₗ[L]
      SchemeModuleGlobalSectionsOver
        (schemeFieldBaseChangeToField (L := L) base)
        ((Scheme.Modules.pullback
          (schemeFieldBaseChangeToOriginal (L := L) base)).obj M) :=
  schemeModuleGlobalSectionsBaseChangeLinearMapOfFinBasis
    base (schemeFieldBaseChangeToField (L := L) base)
      (schemeFieldBaseChangeToOriginal (L := L) base) M

@[simp]
theorem schemeModuleGlobalSectionsFieldBaseChangeLinearMap_one_tmul_finBasis
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    (i : Fin (Module.finrank K (SchemeModuleGlobalSectionsOver base M))) :
    schemeModuleGlobalSectionsFieldBaseChangeLinearMap (L := L) base M
        (1 ⊗ₜ[K] Module.finBasis K
          (SchemeModuleGlobalSectionsOver base M) i) =
      (schemeModuleGlobalSectionsOverEquivSections
        (schemeFieldBaseChangeToField (L := L) base)
        ((Scheme.Modules.pullback
          (schemeFieldBaseChangeToOriginal (L := L) base)).obj M)).symm
        (BundleSectionZeroLocus.pullbackSection
          (schemeFieldBaseChangeToOriginal (L := L) base) M
          (BundleSectionZeroLocus.isIso_pullbackUnitComparison
            (schemeFieldBaseChangeToOriginal (L := L) base))
          (schemeModuleGlobalSectionsOverEquivSections base M
            (Module.finBasis K
              (SchemeModuleGlobalSectionsOver base M) i))) := by
  exact schemeModuleGlobalSectionsBaseChangeLinearMapOfFinBasis_one_tmul_finBasis
    base (schemeFieldBaseChangeToField (L := L) base)
      (schemeFieldBaseChangeToOriginal (L := L) base) M i

/-- The canonical field-base-change equivalence once its literal map has been
proved bijective. -/
noncomputable def schemeModuleGlobalSectionsFieldBaseChangeLinearEquiv
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    (h : Function.Bijective
      (schemeModuleGlobalSectionsFieldBaseChangeLinearMap (L := L) base M)) :
    (L ⊗[K] SchemeModuleGlobalSectionsOver base M) ≃ₗ[L]
      SchemeModuleGlobalSectionsOver
        (schemeFieldBaseChangeToField (L := L) base)
        ((Scheme.Modules.pullback
          (schemeFieldBaseChangeToOriginal (L := L) base)).obj M) :=
  schemeModuleGlobalSectionsBaseChangeLinearEquivOfFinBasis
    base (schemeFieldBaseChangeToField (L := L) base)
      (schemeFieldBaseChangeToOriginal (L := L) base) M h

end

end PfaffianDescent
