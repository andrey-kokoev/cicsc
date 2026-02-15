// Extended AST types for blob support

export interface SpecBlobV0 {
  type: "blob"
  constraints?: {
    maxSize?: number // bytes
    allowedTypes?: string[] // MIME types like ["image/png", "image/jpeg"]
    required?: boolean
  }
  storage?: {
    backend: "r2" | "s3"
    bucket?: string
  }
}

// Extend existing SpecAttrV0 to include blob
export type ExtendedSpecAttrV0 = 
  | { type: "string" | "int" | "float" | "bool" | "time"; optional?: boolean }
  | { type: "blob"; constraints?: SpecBlobV0["constraints"]; storage?: SpecBlobV0["storage"] }
