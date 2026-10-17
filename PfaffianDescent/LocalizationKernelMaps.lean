import Mathlib.Algebra.Module.LocalizedModule.Submodule

namespace PfaffianDescent
section
variable {R M N P Q : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]

/-- The map on kernels induced by a commuting square of module maps. -/
def linearKernelMap (fM : M →ₗ[R] P) (fN : N →ₗ[R] Q) (g : M →ₗ[R] N) (h : P →ₗ[R] Q)
    (hc : h.comp fM = fN.comp g) : g.ker →ₗ[R] h.ker :=
  (fM.comp g.ker.subtype).codRestrict h.ker (fun x => by
    change h (fM x.1) = 0
    rw [show h (fM x.1) = fN (g x.1) from LinearMap.congr_fun hc x.1, x.2, map_zero])

variable (U : Submonoid R) (S : Type*) [CommRing S] [Algebra R S] [IsLocalization U S]
  [Module S P] [IsScalarTower R S P] [Module S Q] [IsScalarTower R S Q]
  (fM : M →ₗ[R] P) (fN : N →ₗ[R] Q) [IsLocalizedModule U fM] [IsLocalizedModule U fN]

include S

/-- Localization preserves kernels for any explicitly identified localized commuting square. -/
theorem linearKernelMap_isLocalizedModule (g : M →ₗ[R] N) (h : P →ₗ[R] Q)
    (hc : h.comp fM = fN.comp g) : IsLocalizedModule U (linearKernelMap fM fN g h hc) := by
  have he : h = IsLocalizedModule.map U fM fN g := by
    apply IsLocalizedModule.linearMap_ext U fM fN
    apply LinearMap.ext
    intro x
    rw [LinearMap.comp_apply, LinearMap.comp_apply, IsLocalizedModule.map_apply]
    exact LinearMap.congr_fun hc x
  subst h
  exact LinearMap.toKerLocalized_isLocalizedModule S U fM fN g

end
end PfaffianDescent
