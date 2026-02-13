export function isAuthorized (req: Request, expectedToken?: string): boolean {
  if (!expectedToken) return true
  const auth = req.headers.get("authorization") ?? ""
  const bearer = auth.startsWith("Bearer ") ? auth.slice("Bearer ".length).trim() : ""
  const alt = req.headers.get("x-cicsc-token") ?? ""
  const provided = bearer || alt
  return provided.length > 0 && provided === expectedToken
}
