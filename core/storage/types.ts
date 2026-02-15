export interface BlobMetadata {
  key: string
  originalName: string
  contentType: string
  size: number
  createdAt: Date
  checksum: string
}

export interface StorageAdapter {
  id: string
  upload(stream: ReadableStream, metadata: Partial<BlobMetadata>): Promise<BlobMetadata>
  getPresignedUrl(key: string, expiresInSeconds?: number): Promise<string>
  delete(key: string): Promise<void>
  validateConfig(): boolean
}

export interface BlobConstraints {
  maxSize?: number // bytes
  allowedTypes?: string[] // MIME types
  required?: boolean
}
