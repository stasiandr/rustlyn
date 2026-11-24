//! What Unity calls by name.
//!
//! To a C# compiler `Update()` on a `MonoBehaviour` is a private method no one
//! calls. Unity calls it, every frame, found by its name through reflection:
//! so do the other messages below, on `MonoBehaviour`, `ScriptableObject`, the
//! editor classes and ECS systems. This is the one list of them; every
//! analysis that needs to know — unused members, outlines, risk of a change —
//! asks here.

use std::collections::HashSet;
use std::sync::OnceLock;

/// The messages the engine sends by name.
pub const MESSAGES: &[&str] = &[
    // Lifecycle
    "Awake",
    "Start",
    "Update",
    "FixedUpdate",
    "LateUpdate",
    "OnEnable",
    "OnDisable",
    "OnDestroy",
    "OnValidate",
    "Reset",
    "OnApplicationFocus",
    "OnApplicationPause",
    "OnApplicationQuit",
    "OnGUI",
    // Physics
    "OnCollisionEnter",
    "OnCollisionStay",
    "OnCollisionExit",
    "OnCollisionEnter2D",
    "OnCollisionStay2D",
    "OnCollisionExit2D",
    "OnTriggerEnter",
    "OnTriggerStay",
    "OnTriggerExit",
    "OnTriggerEnter2D",
    "OnTriggerStay2D",
    "OnTriggerExit2D",
    "OnControllerColliderHit",
    "OnJointBreak",
    "OnJointBreak2D",
    "OnParticleCollision",
    "OnParticleTrigger",
    "OnParticleSystemStopped",
    // Mouse
    "OnMouseDown",
    "OnMouseDrag",
    "OnMouseEnter",
    "OnMouseExit",
    "OnMouseOver",
    "OnMouseUp",
    "OnMouseUpAsButton",
    // Rendering
    "OnBecameVisible",
    "OnBecameInvisible",
    "OnWillRenderObject",
    "OnRenderObject",
    "OnPreCull",
    "OnPreRender",
    "OnPostRender",
    "OnRenderImage",
    "OnDrawGizmos",
    "OnDrawGizmosSelected",
    // Animation and audio
    "OnAnimatorIK",
    "OnAnimatorMove",
    "OnAudioFilterRead",
    "OnDidApplyAnimationProperties",
    // Hierarchy and UI
    "OnTransformParentChanged",
    "OnTransformChildrenChanged",
    "OnBeforeTransformParentChanged",
    "OnRectTransformDimensionsChange",
    "OnCanvasGroupChanged",
    // Editor
    "OnInspectorGUI",
    "OnSceneGUI",
    "OnPreviewGUI",
    "HasPreviewGUI",
    "OnHeaderGUI",
    "CreateInspectorGUI",
    "CreateGUI",
    "OnFocus",
    "OnLostFocus",
    "OnHierarchyChange",
    "OnProjectChange",
    "OnSelectionChange",
    "OnInspectorUpdate",
    "OnWizardCreate",
    "OnWizardUpdate",
    "OnWizardOtherButton",
    "OnPreprocessTexture",
    "OnPostprocessTexture",
    "OnPreprocessModel",
    "OnPostprocessModel",
    "OnPreprocessAudio",
    "OnPostprocessAudio",
    "OnPostprocessAllAssets",
    // ECS
    "OnCreate",
    "OnUpdate",
    "OnStartRunning",
    "OnStopRunning",
];

/// The messages sent every frame: a mistake or a slow line in one of them
/// shows at once.
pub const PER_FRAME: &[&str] = &[
    "Update",
    "LateUpdate",
    "FixedUpdate",
    "OnGUI",
    "OnRenderObject",
    "OnPreRender",
    "OnPostRender",
];

/// The classes whose subclasses are sent [`MESSAGES`].
pub const MESSAGE_RECEIVERS: &[&str] = &[
    "MonoBehaviour",
    "ScriptableObject",
    "Editor",
    "EditorWindow",
    "StateMachineBehaviour",
    "NetworkBehaviour",
];

/// Attributes that put a field into Unity's serialization, and with it into
/// the Inspector.
pub const SERIALIZATION_ATTRIBUTES: [&str; 2] = ["SerializeField", "SerializeReference"];

/// Whether Unity calls a method of this name by itself.
#[must_use]
pub fn is_message(name: &str) -> bool {
    static SET: OnceLock<HashSet<&'static str>> = OnceLock::new();
    SET.get_or_init(|| MESSAGES.iter().copied().collect())
        .contains(name)
}

/// Whether Unity calls a method of this name every frame.
#[must_use]
pub fn is_per_frame(name: &str) -> bool {
    PER_FRAME.contains(&name)
}

/// Whether subclasses of a class of this name are sent messages.
#[must_use]
pub fn is_message_receiver(name: &str) -> bool {
    MESSAGE_RECEIVERS.contains(&name)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn every_frame_message_is_a_message() {
        assert!(PER_FRAME.iter().all(|name| is_message(name)));
        assert!(is_message("Awake") && is_message("OnCollisionStay2D") && is_message("OnUpdate"));
        assert!(!is_message("Run") && !is_per_frame("Start") && is_per_frame("LateUpdate"));
        assert!(is_message_receiver("MonoBehaviour") && !is_message_receiver("Object"));
        let unique: HashSet<&str> = MESSAGES.iter().copied().collect();
        assert_eq!(unique.len(), MESSAGES.len(), "no name twice");
    }
}
