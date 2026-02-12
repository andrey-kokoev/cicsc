import path from "node:path"

function shouldTryExtensionResolution(specifier) {
  if (specifier.startsWith("node:")) return false
  if (specifier.startsWith("data:")) return false
  if (specifier.startsWith("http:")) return false
  if (specifier.startsWith("https:")) return false
  if (specifier.startsWith("file:")) return true
  if (specifier.startsWith("./") || specifier.startsWith("../") || specifier.startsWith("/")) return true
  return false
}

function hasKnownExtension(specifier) {
  if (specifier.startsWith("file:")) {
    try {
      const u = new URL(specifier)
      return path.extname(u.pathname) !== ""
    } catch {
      return false
    }
  }
  return path.extname(specifier) !== ""
}

export async function resolve(specifier, context, nextResolve) {
  try {
    return await nextResolve(specifier, context)
  } catch (err) {
    if (!err || err.code !== "ERR_MODULE_NOT_FOUND") {
      throw err
    }

    if (!shouldTryExtensionResolution(specifier) || hasKnownExtension(specifier)) {
      throw err
    }

    const candidates = [
      `${specifier}.ts`,
      `${specifier}.js`,
      `${specifier}/index.ts`,
      `${specifier}/index.js`,
    ]

    for (const candidate of candidates) {
      try {
        return await nextResolve(candidate, context)
      } catch {
        // Try next candidate.
      }
    }

    throw err
  }
}
