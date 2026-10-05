import CGLMP5.CertificateHeaderData

namespace CGLMP5.CertificateSource
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 20000

theorem header_gamma_decode : sourceHeaderGamma.mapM ChunkScalar.decode = some gammaRaw := by
  decide +kernel

theorem header_mu_box_decode : sourceHeaderMuBox.decode = some muBox := by
  decide +kernel

theorem header_s_box_decode : sourceHeaderSBox.decode = some sBox := by
  decide +kernel

theorem header_u_box_decode : sourceHeaderUBox.decode = some uBox := by
  decide +kernel

theorem header_gamma_text_decode :
    (sourceHeaderGamma.map ChunkScalar.toText).mapM TextScalar.decode = some gammaRaw := by
  simpa only [List.mapM_map, Function.comp_def] using
    option_mapM_sound ChunkScalar.decode (fun s => s.toText.decode)
      (fun s r h => ChunkScalar.decode_sound h) sourceHeaderGamma gammaRaw header_gamma_decode

theorem header_mu_box_text_decode : sourceHeaderMuBox.toText.decode = some muBox :=
  ChunkBox.decode_sound header_mu_box_decode

theorem header_s_box_text_decode : sourceHeaderSBox.toText.decode = some sBox :=
  ChunkBox.decode_sound header_s_box_decode

theorem header_u_box_text_decode : sourceHeaderUBox.toText.decode = some uBox :=
  ChunkBox.decode_sound header_u_box_decode

end CGLMP5.CertificateSource
