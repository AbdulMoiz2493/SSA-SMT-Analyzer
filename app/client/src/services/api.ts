import axios from 'axios';

const API_URL = 'http://localhost:5000/api';

export interface AnalysisRequest {
  mode: 'verification' | 'equivalence';
  program1: string;
  program2?: string;
  unrollDepth: number;
}

export interface SSAResult {
  original: any[];
  transformed: string[];
  optimized: string[];
}

export interface AnalysisResponse {
  ssa: {
    ssa1: SSAResult;
    ssa2?: SSAResult;
  };
  smt: string;
  status: 'verified' | 'not_verified' | 'equivalent' | 'not_equivalent' | 'error' | 'gemini_processed';
  results?: {
    sat?: 'sat' | 'unsat' | 'error';
    verified?: boolean;
    equivalent?: boolean;
    interpretation?: string;
    counterexample?: Record<string, string>;
    model?: Record<string, string>;
  };
  error?: string;
  Debug?: string;
  apiSource?: string;
  source?: string;
  fallbackCheck?: string;
}

export const analyzePrograms = async (request: AnalysisRequest): Promise<AnalysisResponse> => {
  try {
    const response = await axios.post(`${API_URL}/analyze`, request);
    return response.data as AnalysisResponse;
  } catch (error) {
    if (axios.isAxiosError(error)) {
      console.error('Axios error:', error.response?.data, error.response?.status);
      throw new Error(
        error.response?.data?.error || `Failed to analyze programs: ${error.message}`
      );
    }
    console.error('Unexpected error:', error);
    throw new Error(`Failed to analyze programs: ${error.message}`);
  }
};