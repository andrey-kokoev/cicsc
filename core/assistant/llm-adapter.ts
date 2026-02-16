//==============================================================================
// LLM Adapter Interface
//
// BG1.5: Abstract provider interface for any LLM
// BG1.6: OpenAI provider implementation  
// BG1.7: Ollama provider implementation (local models)
// BG1.8: Add embed() method to LLMProvider interface
// BG1.12: Add request timeout configuration
// BG1.13: Fix fragile private state access in LLMInterviewEngine
// BG1.14: Add error handling and output validation
// BG1.15: Add provider-side chat cache support (cache_by)
//==============================================================================

export interface LLMMessage {
  role: "system" | "user" | "assistant"
  content: string
}

export interface LLMResponse {
  content: string
  model: string
  usage?: {
    promptTokens: number
    completionTokens: number
    totalTokens: number
  }
}

export interface LLMEmbedding {
  embedding: number[]
  model: string
  tokens?: number
}

export interface LLMTimeoutConfig {
  requestMs: number
  connectMs?: number
}

export interface LLMOptions {
  model?: string
  temperature?: number
  maxTokens?: number
  stop?: string[]
  cacheBy?: string
  timeout?: LLMTimeoutConfig
}

export interface LLMProvider {
  name: string
  chat(messages: LLMMessage[], options?: LLMOptions): Promise<LLMResponse>
  embed(text: string, options?: { model?: string }): Promise<LLMEmbedding>
  health(): Promise<boolean>
}

export type LLMProviderName = "openai" | "ollama" | "anthropic" | "openrouter" | "kimi" | "qwen" | "azure-openai" | "gemini" | "local"

export interface LLMConfig {
  provider: LLMProviderName
  apiKey?: string
  baseUrl?: string
  defaultModel?: string
  maxTokens?: number
  temperature?: number
  timeout?: LLMTimeoutConfig
}

const DEFAULT_TIMEOUT_CONFIG: LLMTimeoutConfig = {
  requestMs: 30000,
  connectMs: 10000
}

function createAbortableFetch(
  url: string,
  options: RequestInit & { timeout?: number }
): { controller: AbortController; promise: Promise<Response> } {
  const controller = new AbortController()
  const timeout = options.timeout || DEFAULT_TIMEOUT_CONFIG.requestMs
  
  const timeoutId = setTimeout(() => controller.abort(), timeout)
  
  const promise = fetch(url, {
    ...options,
    signal: controller.signal
  }).finally(() => clearTimeout(timeoutId))
  
  return { controller, promise }
}

function validateResponseContent(content: string): string {
  if (!content || content.trim().length === 0) {
    throw new Error("LLM response content is empty")
  }
  return content.trim()
}

function calculateCacheKey(messages: LLMMessage[], options?: LLMOptions): string {
  const cacheKeyParts = [
    options?.model || "",
    String(options?.temperature ?? ""),
    String(options?.maxTokens ?? ""),
    ...messages.map(m => `${m.role}:${m.content}`)
  ]
  
  let hash = 0
  for (const part of cacheKeyParts) {
    const charCodes = part.split("").map(c => c.charCodeAt(0))
    for (const code of charCodes) {
      hash = ((hash << 5) - hash) + code
      hash = hash & hash
    }
  }
  
  return Math.abs(hash).toString(36)
}

class SimpleCache {
  private cache = new Map<string, { value: LLMResponse; expiry: number }>()
  private ttlSeconds: number
  private keyPrefix: string

  constructor(ttlSeconds: number = 300, keyPrefix: string = "llm:") {
    this.ttlSeconds = ttlSeconds
    this.keyPrefix = keyPrefix
  }

  get(key: string): LLMResponse | null {
    const item = this.cache.get(this.keyPrefix + key)
    if (!item) return null
    
    if (Date.now() > item.expiry) {
      this.cache.delete(this.keyPrefix + key)
      return null
    }
    
    return item.value
  }

  set(key: string, value: LLMResponse): void {
    this.cache.set(this.keyPrefix + key, {
      value,
      expiry: Date.now() + (this.ttlSeconds * 1000)
    })
  }

  clear(): void {
    this.cache.clear()
  }
}

/**
 * Factory to create LLM providers
 */
export function createLLMProvider(config: LLMConfig): LLMProvider {
  switch (config.provider) {
    case "openai":
      return new OpenAIProvider(config)
    case "ollama":
      return new OllamaProvider(config)
    case "anthropic":
      return new AnthropicProvider(config)
    case "openrouter":
      return new OpenRouterProvider(config)
    case "kimi":
      return new KimiProvider(config)
    case "qwen":
      return new QwenProvider(config)
    case "azure-openai":
      return new AzureOpenAIProvider(config)
    case "gemini":
      return new GeminiProvider(config)
    default:
      throw new Error(`Unknown LLM provider: ${config.provider}`)
  }
}

//==============================================================================
// OpenAI Provider Implementation (BG1.6)
//==============================================================================

export class OpenAIProvider implements LLMProvider {
  name = "openai"
  private apiKey: string
  private baseUrl: string
  private defaultModel: string

  constructor(config: LLMConfig) {
    this.apiKey = config.apiKey || (typeof process !== "undefined" ? process.env.OPENAI_API_KEY : "") || ""
    this.baseUrl = config.baseUrl || "https://api.openai.com/v1"
    this.defaultModel = config.defaultModel || "gpt-4o"
    
    if (!this.apiKey) {
      throw new Error("OpenAI API key required. Set OPENAI_API_KEY or pass apiKey in config.")
    }
  }

  async chat(messages: LLMMessage[], options?: LLMOptions): Promise<LLMResponse> {
    const response = await fetch(`${this.baseUrl}/chat/completions`, {
      method: "POST",
      headers: {
        "Content-Type": "application/json",
        "Authorization": `Bearer ${this.apiKey}`
      },
      body: JSON.stringify({
        model: options?.model || this.defaultModel,
        messages: messages.map(m => ({ role: m.role, content: m.content })),
        temperature: options?.temperature ?? 0.7,
        max_tokens: options?.maxTokens || this.defaultModel,
        stop: options?.stop
      })
    })

    if (!response.ok) {
      const error = await response.text()
      throw new Error(`OpenAI API error: ${response.status} - ${error}`)
    }

    const data = await response.json()
    const choice = data.choices[0]

    return {
      content: choice.message.content,
      model: data.model,
      usage: data.usage ? {
        promptTokens: data.usage.prompt_tokens,
        completionTokens: data.usage.completion_tokens,
        totalTokens: data.usage.total_tokens
      } : undefined
    }
  }

  async health(): Promise<boolean> {
    try {
      const response = await fetch(`${this.baseUrl}/models`, {
        headers: { "Authorization": `Bearer ${this.apiKey}` }
      })
      return response.ok
    } catch {
      return false
    }
  }

  async embed(text: string, options?: { model?: string }): Promise<LLMEmbedding> {
    const { controller, promise } = createAbortableFetch(
      `${this.baseUrl}/embeddings`,
      {
        method: "POST",
        headers: {
          "Content-Type": "application/json",
          "Authorization": `Bearer ${this.apiKey}`
        },
        body: JSON.stringify({
          model: options?.model || "text-embedding-3-small",
          input: text
        }),
        timeout: DEFAULT_TIMEOUT_CONFIG.requestMs
      }
    )

    try {
      const response = await promise

      if (!response.ok) {
        const error = await response.text()
        throw new Error(`OpenAI API error: ${response.status} - ${error}`)
      }

      const data = await response.json()
      const embedding = data.data[0]?.embedding

      if (!embedding) {
        throw new Error("No embedding returned from OpenAI")
      }

      return {
        embedding,
        model: data.model,
        tokens: data.usage?.total_tokens
      }
    } catch (error: any) {
      if (error.name === "AbortError") {
        throw new Error(`Request timeout after ${DEFAULT_TIMEOUT_CONFIG.requestMs}ms`)
      }
      throw error
    }
  }
}

//==============================================================================
// Ollama Provider Implementation (BG1.7)
//==============================================================================

export class OllamaProvider implements LLMProvider {
  name = "ollama"
  private baseUrl: string
  private defaultModel: string

  constructor(config: LLMConfig) {
    this.baseUrl = config.baseUrl || (typeof process !== "undefined" ? process.env.OLLAMA_BASE_URL : "") || "http://localhost:11434"
    this.defaultModel = config.defaultModel || "llama2"
  }

  async chat(messages: LLMMessage[], options?: LLMOptions): Promise<LLMResponse> {
    const response = await fetch(`${this.baseUrl}/api/chat`, {
      method: "POST",
      headers: { "Content-Type": "application/json" },
      body: JSON.stringify({
        model: options?.model || this.defaultModel,
        messages: messages.map(m => ({ role: m.role, content: m.content })),
        stream: false,
        options: {
          temperature: options?.temperature ?? 0.7,
          num_predict: options?.maxTokens || 2048,
          stop: options?.stop
        }
      })
    })

    if (!response.ok) {
      const error = await response.text()
      throw new Error(`Ollama API error: ${response.status} - ${error}`)
    }

    const data = await response.json()

    return {
      content: data.message.content,
      model: data.model || this.defaultModel,
      usage: data.prompt_eval_count !== undefined || data.eval_count !== undefined ? {
        promptTokens: data.prompt_eval_count || 0,
        completionTokens: data.eval_count || 0,
        totalTokens: (data.prompt_eval_count || 0) + (data.eval_count || 0)
      } : undefined
    }
  }

  async health(): Promise<boolean> {
    try {
      const response = await fetch(`${this.baseUrl}/api/tags`)
      return response.ok
    } catch {
      return false
    }
  }

  async embed(text: string, options?: { model?: string }): Promise<LLMEmbedding> {
    const { controller, promise } = createAbortableFetch(
      `${this.baseUrl}/api/embeddings`,
      {
        method: "POST",
        headers: { "Content-Type": "application/json" },
        body: JSON.stringify({
          model: options?.model || this.defaultModel,
          prompt: text
        }),
        timeout: DEFAULT_TIMEOUT_CONFIG.requestMs
      }
    )

    try {
      const response = await promise

      if (!response.ok) {
        const error = await response.text()
        throw new Error(`Ollama API error: ${response.status} - ${error}`)
      }

      const data = await response.json()

      if (!data.embedding) {
        throw new Error("No embedding returned from Ollama")
      }

      return {
        embedding: data.embedding,
        model: data.model || this.defaultModel
      }
    } catch (error: any) {
      if (error.name === "AbortError") {
        throw new Error(`Request timeout after ${DEFAULT_TIMEOUT_CONFIG.requestMs}ms`)
      }
      throw error
    }
  }
}

//==============================================================================
// Anthropic Provider Implementation (BG1.16)
//==============================================================================

export class AnthropicProvider implements LLMProvider {
  name = "anthropic"
  private apiKey: string
  private baseUrl: string
  private defaultModel: string

  constructor(config: LLMConfig) {
    this.apiKey = config.apiKey || (typeof process !== "undefined" ? process.env.ANTHROPIC_API_KEY : "") || ""
    this.baseUrl = config.baseUrl || "https://api.anthropic.com/v1"
    this.defaultModel = config.defaultModel || "claude-3-5-sonnet-20241022"

    if (!this.apiKey) {
      throw new Error("Anthropic API key required. Set ANTHROPIC_API_KEY or pass apiKey in config.")
    }
  }

  async chat(messages: LLMMessage[], options?: LLMOptions): Promise<LLMResponse> {
    // Anthropic uses a different message format
    const systemMessage = messages.find(m => m.role === "system")
    const userMessages = messages.filter(m => m.role !== "system").map(m => ({
      role: m.role === "assistant" ? "assistant" : "user",
      content: m.content
    }))

    const response = await fetch(`${this.baseUrl}/messages`, {
      method: "POST",
      headers: {
        "Content-Type": "application/json",
        "x-api-key": this.apiKey,
        "anthropic-version": "2023-06-01"
      },
      body: JSON.stringify({
        model: options?.model || this.defaultModel,
        max_tokens: options?.maxTokens || 4096,
        system: systemMessage?.content,
        messages: userMessages
      })
    })

    if (!response.ok) {
      const error = await response.text()
      throw new Error(`Anthropic API error: ${response.status} - ${error}`)
    }

    const data = await response.json()
    const content = data.content[0]?.text || ""

    return {
      content,
      model: data.model,
      usage: data.usage ? {
        promptTokens: data.usage.input_tokens,
        completionTokens: data.usage.output_tokens,
        totalTokens: data.usage.input_tokens + data.usage.output_tokens
      } : undefined
    }
  }

  async health(): Promise<boolean> {
    try {
      // Anthropic doesn't have a health endpoint, so we'll just check if we can authenticate
      const response = await fetch(`${this.baseUrl}/messages`, {
        method: "POST",
        headers: {
          "Content-Type": "application/json",
          "x-api-key": this.apiKey,
          "anthropic-version": "2023-06-01"
        },
        body: JSON.stringify({
          model: this.defaultModel,
          max_tokens: 1,
          messages: [{ role: "user", content: "." }]
        })
      })
      // We expect this to succeed or fail with auth error
      return response.status !== 401
    } catch {
      return false
    }
  }

  async embed(_text: string, _options?: { model?: string }): Promise<LLMEmbedding> {
    throw new Error("Anthropic does not support embeddings. Use OpenAI or Ollama.")
  }
}

//==============================================================================
// OpenRouter Provider Implementation (BG1.17) - 100+ models
//==============================================================================

export class OpenRouterProvider implements LLMProvider {
  name = "openrouter"
  private apiKey: string
  private baseUrl: string
  private defaultModel: string

  constructor(config: LLMConfig) {
    this.apiKey = config.apiKey || (typeof process !== "undefined" ? process.env.OPENROUTER_API_KEY : "") || ""
    this.baseUrl = config.baseUrl || "https://openrouter.ai/api/v1"
    this.defaultModel = config.defaultModel || "openai/gpt-4o"

    if (!this.apiKey) {
      throw new Error("OpenRouter API key required. Set OPENROUTER_API_KEY or pass apiKey in config.")
    }
  }

  async chat(messages: LLMMessage[], options?: LLMOptions): Promise<LLMResponse> {
    const response = await fetch(`${this.baseUrl}/chat/completions`, {
      method: "POST",
      headers: {
        "Content-Type": "application/json",
        "Authorization": `Bearer ${this.apiKey}`,
        "HTTP-Referer": "https://cicsc.dev",
        "X-Title": "CICSC"
      },
      body: JSON.stringify({
        model: options?.model || this.defaultModel,
        messages: messages.map(m => ({ role: m.role, content: m.content })),
        temperature: options?.temperature ?? 0.7,
        max_tokens: options?.maxTokens || 4096,
        stop: options?.stop
      })
    })

    if (!response.ok) {
      const error = await response.text()
      throw new Error(`OpenRouter API error: ${response.status} - ${error}`)
    }

    const data = await response.json()
    const choice = data.choices[0]

    return {
      content: choice.message.content,
      model: data.model,
      usage: data.usage ? {
        promptTokens: data.usage.prompt_tokens,
        completionTokens: data.usage.completion_tokens,
        totalTokens: data.usage.total_tokens
      } : undefined
    }
  }

  async health(): Promise<boolean> {
    try {
      const response = await fetch(`${this.baseUrl}/models`, {
        headers: { "Authorization": `Bearer ${this.apiKey}` }
      })
      return response.ok
    } catch {
      return false
    }
  }

  async embed(_text: string, _options?: { model?: string }): Promise<LLMEmbedding> {
    throw new Error("OpenRouter does not support embeddings. Use OpenAI or Ollama.")
  }
}

//==============================================================================
// Kimi Provider Implementation (BG1.18) - Moonshot AI
//==============================================================================

export class KimiProvider implements LLMProvider {
  name = "kimi"
  private apiKey: string
  private baseUrl: string
  private defaultModel: string

  constructor(config: LLMConfig) {
    this.apiKey = config.apiKey || (typeof process !== "undefined" ? process.env.KIMI_API_KEY : "") || ""
    this.baseUrl = config.baseUrl || "https://api.moonshot.cn/v1"
    this.defaultModel = config.defaultModel || "moonshot-v1-8k"

    if (!this.apiKey) {
      throw new Error("Kimi API key required. Set KIMI_API_KEY or pass apiKey in config.")
    }
  }

  async chat(messages: LLMMessage[], options?: LLMOptions): Promise<LLMResponse> {
    const response = await fetch(`${this.baseUrl}/chat/completions`, {
      method: "POST",
      headers: {
        "Content-Type": "application/json",
        "Authorization": `Bearer ${this.apiKey}`
      },
      body: JSON.stringify({
        model: options?.model || this.defaultModel,
        messages: messages.map(m => ({ role: m.role, content: m.content })),
        temperature: options?.temperature ?? 0.7,
        max_tokens: options?.maxTokens || 4096,
        stop: options?.stop
      })
    })

    if (!response.ok) {
      const error = await response.text()
      throw new Error(`Kimi API error: ${response.status} - ${error}`)
    }

    const data = await response.json()
    const choice = data.choices[0]

    return {
      content: choice.message.content,
      model: data.model,
      usage: data.usage ? {
        promptTokens: data.usage.prompt_tokens,
        completionTokens: data.usage.completion_tokens,
        totalTokens: data.usage.total_tokens
      } : undefined
    }
  }

  async health(): Promise<boolean> {
    try {
      const response = await fetch(`${this.baseUrl}/models`, {
        headers: { "Authorization": `Bearer ${this.apiKey}` }
      })
      return response.ok
    } catch {
      return false
    }
  }

  async embed(_text: string, _options?: { model?: string }): Promise<LLMEmbedding> {
    throw new Error("Kimi does not support embeddings. Use OpenAI or Ollama.")
  }
}

//==============================================================================
// Qwen Provider Implementation (BG1.19) - Alibaba
//==============================================================================

export class QwenProvider implements LLMProvider {
  name = "qwen"
  private apiKey: string
  private baseUrl: string
  private defaultModel: string

  constructor(config: LLMConfig) {
    this.apiKey = config.apiKey || (typeof process !== "undefined" ? process.env.DASHSCOPE_API_KEY : "") || ""
    this.baseUrl = config.baseUrl || "https://dashscope.aliyuncs.com/compatible-mode/v1"
    this.defaultModel = config.defaultModel || "qwen-plus"

    if (!this.apiKey) {
      throw new Error("Qwen/DashScope API key required. Set DASHSCOPE_API_KEY or pass apiKey in config.")
    }
  }

  async chat(messages: LLMMessage[], options?: LLMOptions): Promise<LLMResponse> {
    const response = await fetch(`${this.baseUrl}/chat/completions`, {
      method: "POST",
      headers: {
        "Content-Type": "application/json",
        "Authorization": `Bearer ${this.apiKey}`
      },
      body: JSON.stringify({
        model: options?.model || this.defaultModel,
        messages: messages.map(m => ({ role: m.role, content: m.content })),
        temperature: options?.temperature ?? 0.7,
        max_tokens: options?.maxTokens || 4096,
        stop: options?.stop
      })
    })

    if (!response.ok) {
      const error = await response.text()
      throw new Error(`Qwen/DashScope API error: ${response.status} - ${error}`)
    }

    const data = await response.json()
    const choice = data.choices[0]

    return {
      content: choice.message.content,
      model: data.model,
      usage: data.usage ? {
        promptTokens: data.usage.prompt_tokens,
        completionTokens: data.usage.completion_tokens,
        totalTokens: data.usage.total_tokens
      } : undefined
    }
  }

  async health(): Promise<boolean> {
    try {
      const response = await fetch(`${this.baseUrl}/models`, {
        headers: { "Authorization": `Bearer ${this.apiKey}` }
      })
      return response.ok
    } catch {
      return false
    }
  }

  async embed(_text: string, _options?: { model?: string }): Promise<LLMEmbedding> {
    throw new Error("Qwen does not support embeddings. Use OpenAI or Ollama.")
  }
}

//==============================================================================
// Azure OpenAI Provider Implementation (BG1.20)
//==============================================================================

export class AzureOpenAIProvider implements LLMProvider {
  name = "azure-openai"
  private apiKey: string
  private baseUrl: string
  private deploymentName: string
  private apiVersion: string

  constructor(config: LLMConfig) {
    this.apiKey = config.apiKey || (typeof process !== "undefined" ? process.env.AZURE_OPENAI_API_KEY : "") || ""
    this.baseUrl = config.baseUrl || (typeof process !== "undefined" ? process.env.AZURE_OPENAI_ENDPOINT : "") || ""
    this.deploymentName = config.defaultModel || (typeof process !== "undefined" ? process.env.AZURE_OPENAI_DEPLOYMENT_NAME : "") || "gpt-4"
    this.apiVersion = "2024-02-15-preview"

    if (!this.apiKey || !this.baseUrl) {
      throw new Error("Azure OpenAI requires API key and endpoint. Set AZURE_OPENAI_API_KEY and AZURE_OPENAI_ENDPOINT.")
    }
  }

  async chat(messages: LLMMessage[], options?: LLMOptions): Promise<LLMResponse> {
    const url = `${this.baseUrl}/openai/deployments/${this.deploymentName}/chat/completions?api-version=${this.apiVersion}`
    
    const response = await fetch(url, {
      method: "POST",
      headers: {
        "Content-Type": "application/json",
        "api-key": this.apiKey
      },
      body: JSON.stringify({
        messages: messages.map(m => ({ role: m.role, content: m.content })),
        temperature: options?.temperature ?? 0.7,
        max_tokens: options?.maxTokens || 4096,
        stop: options?.stop
      })
    })

    if (!response.ok) {
      const error = await response.text()
      throw new Error(`Azure OpenAI API error: ${response.status} - ${error}`)
    }

    const data = await response.json()
    const choice = data.choices[0]

    return {
      content: choice.message.content,
      model: this.deploymentName,
      usage: data.usage ? {
        promptTokens: data.usage.prompt_tokens,
        completionTokens: data.usage.completion_tokens,
        totalTokens: data.usage.total_tokens
      } : undefined
    }
  }

  async health(): Promise<boolean> {
    try {
      const url = `${this.baseUrl}/openai/deployments/${this.deploymentName}?api-version=${this.apiVersion}`
      const response = await fetch(url, {
        headers: { "api-key": this.apiKey }
      })
      return response.ok
    } catch {
      return false
    }
  }

  async embed(_text: string, _options?: { model?: string }): Promise<LLMEmbedding> {
    throw new Error("Azure OpenAI does not support embeddings. Use OpenAI or Ollama.")
  }
}

//==============================================================================
// Gemini Provider Implementation (BG1.21) - Google
//==============================================================================

export class GeminiProvider implements LLMProvider {
  name = "gemini"
  private apiKey: string
  private baseUrl: string
  private defaultModel: string

  constructor(config: LLMConfig) {
    this.apiKey = config.apiKey || (typeof process !== "undefined" ? process.env.GEMINI_API_KEY : "") || ""
    this.baseUrl = config.baseUrl || "https://generativelanguage.googleapis.com/v1beta"
    this.defaultModel = config.defaultModel || "gemini-1.5-pro"

    if (!this.apiKey) {
      throw new Error("Gemini API key required. Set GEMINI_API_KEY or pass apiKey in config.")
    }
  }

  async chat(messages: LLMMessage[], options?: LLMOptions): Promise<LLMResponse> {
    // Gemini uses a different message format
    const contents = messages
      .filter(m => m.role !== "system")
      .map(m => ({
        role: m.role === "assistant" ? "model" : "user",
        parts: [{ text: m.content }]
      }))

    const systemInstruction = messages.find(m => m.role === "system")?.content

    const url = `${this.baseUrl}/models/${options?.model || this.defaultModel}:generateContent?key=${this.apiKey}`
    
    const body: any = {
      contents,
      generationConfig: {
        temperature: options?.temperature ?? 0.7,
        maxOutputTokens: options?.maxTokens || 4096,
        stopSequences: options?.stop
      }
    }

    if (systemInstruction) {
      body.systemInstruction = {
        parts: [{ text: systemInstruction }]
      }
    }

    const response = await fetch(url, {
      method: "POST",
      headers: {
        "Content-Type": "application/json"
      },
      body: JSON.stringify(body)
    })

    if (!response.ok) {
      const error = await response.text()
      throw new Error(`Gemini API error: ${response.status} - ${error}`)
    }

    const data = await response.json()
    const content = data.candidates?.[0]?.content?.parts?.[0]?.text || ""

    return {
      content,
      model: this.defaultModel,
      usage: data.usageMetadata ? {
        promptTokens: data.usageMetadata.promptTokenCount,
        completionTokens: data.usageMetadata.candidatesTokenCount,
        totalTokens: data.usageMetadata.totalTokenCount
      } : undefined
    }
  }

  async health(): Promise<boolean> {
    try {
      const url = `${this.baseUrl}/models?key=${this.apiKey}`
      const response = await fetch(url)
      return response.ok
    } catch {
      return false
    }
  }

  async embed(_text: string, _options?: { model?: string }): Promise<LLMEmbedding> {
    throw new Error("Gemini does not support embeddings. Use OpenAI or Ollama.")
  }
}

//==============================================================================
// Integration with Interview Engine
//==============================================================================

import { InterviewEngine } from "./interview-engine"

export class LLMInterviewEngine {
  private provider: LLMProvider
  private interview: InterviewEngine

  constructor(provider: LLMProvider) {
    this.provider = provider
    this.interview = new InterviewEngine()
  }

  async process(input: string): Promise<string> {
    const localResponse = this.interview.processInput(input)
    if (localResponse) {
      return localResponse
    }

    const state = this.interview.getState()
    if (state.currentStep === "CONFIRM") {
      return this.interview.getSummary()
    }

    return this.interview.getNextQuestion()
  }

  async extractEntities(unstructured: string): Promise<{
    entities: string[]
    states: Record<string, string[]>
    attributes: Record<string, string[]>
  }> {
    const prompt = `Extract entity definitions from this description. Return JSON with:
- entities: array of entity names
- states: object mapping entity names to their states
- attributes: object mapping entity names to their attributes (with types)

Input: ${unstructured}

Respond with valid JSON only.`

    const response = await this.provider.chat([
      { role: "system", content: "You extract structured entity definitions from natural language." },
      { role: "user", content: prompt }
    ])

    try {
      return JSON.parse(response.content)
    } catch {
      return { entities: [], states: {}, attributes: {} }
    }
  }

  /**
   * Use LLM to generate migration from natural language change request
   */
  async generateMigration(currentSpec: string, changeRequest: string): Promise<string> {
    const prompt = `Given this CICSC specification:

\`\`\`
${currentSpec}
\`\`\`

Generate a migration specification for this change request:

${changeRequest}

Respond with a migration spec in YAML format with: from_version, to_version, on_type, event_transforms.`

    const response = await this.provider.chat([
      { role: "system", content: "You generate CICSC migration specifications." },
      { role: "user", content: prompt }
    ])

    return response.content
  }
}
