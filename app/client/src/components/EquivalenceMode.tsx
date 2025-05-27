import React, { useState } from 'react';
import { Button } from "@/components/ui/button";
import { 
  Select,
  SelectContent,
  SelectItem,
  SelectTrigger,
  SelectValue
} from "@/components/ui/select";
import { Input } from "@/components/ui/input";
import { Label } from "@/components/ui/label";
import CodeEditor from './CodeEditor';
import AnalysisResults from './AnalysisResults';
import { analyzePrograms, AnalysisResponse } from '@/services/api';
import { examplePrograms } from '@/utils/examplePrograms';
import { toast } from "@/components/ui/use-toast";
import { Layers } from "lucide-react";

const EquivalenceMode: React.FC = () => {
  const [program1, setProgram1] = useState<string>('');
  const [program2, setProgram2] = useState<string>('');
  const [unrollDepth, setUnrollDepth] = useState<number>(3);
  const [isLoading, setIsLoading] = useState<boolean>(false);
  const [results, setResults] = useState<AnalysisResponse | null>(null);

  const handleSelectExample = (value: string) => {
    const example = examplePrograms.equivalence.find(ex => ex.name === value);
    if (example) {
      setProgram1(example.program1);
      setProgram2(example.program2);
    }
  };

  const handleAnalyze = async () => {
    if (!program1.trim() || !program2.trim()) {
      toast({
        title: "Error",
        description: "Please enter both programs to analyze for equivalence",
        variant: "destructive",
      });
      return;
    }

    setIsLoading(true);
    try {
      console.log('Analyzing programs:', { program1, program2 });
      const response = await analyzePrograms({
        mode: 'equivalence',
        program1,
        program2,
        unrollDepth
      });
      console.log('Analysis response:', response);
      setResults(response);
    } catch (error) {
      console.error('Error during analysis:', error);
      toast({
        title: "Analysis Failed",
        description: error.message || "An error occurred during program analysis",
        variant: "destructive",
      });
    } finally {
      setIsLoading(false);
    }
  };

  return (
    <div className="space-y-6">
      <div className="bg-slate-50 dark:bg-slate-800/50 rounded-xl p-6 border border-slate-100 dark:border-slate-800">
        <h2 className="text-lg font-medium mb-4 text-slate-800 dark:text-slate-200">Program Equivalence Check</h2>
        <div className="flex flex-col md:flex-row gap-4 items-end">
          <div className="w-full md:w-1/3">
            <Label htmlFor="example-select" className="text-slate-700 dark:text-slate-300">Choose Example Programs</Label>
            <Select onValueChange={handleSelectExample}>
              <SelectTrigger id="example-select" className="bg-white dark:bg-slate-800 border-slate-200 dark:border-slate-700">
                <SelectValue placeholder="Select example programs" />
              </SelectTrigger>
              <SelectContent className="bg-white dark:bg-slate-800 border-slate-200 dark:border-slate-700">
                {examplePrograms.equivalence.map((example) => (
                  <SelectItem key={example.name} value={example.name}>
                    {example.name}
                  </SelectItem>
                ))}
              </SelectContent>
            </Select>
          </div>
          <div className="w-full md:w-1/3">
            <Label htmlFor="unroll-depth" className="text-slate-700 dark:text-slate-300">Loop Unroll Depth</Label>
            <Input
              id="unroll-depth"
              type="number"
              value={unrollDepth}
              onChange={(e) => setUnrollDepth(Math.max(1, parseInt(e.target.value) || 1))}
              min={1}
              className="bg-white dark:bg-slate-800 border-slate-200 dark:border-slate-700"
            />
          </div>
          <Button 
            onClick={handleAnalyze} 
            disabled={isLoading}
            className="bg-purple-600 hover:bg-purple-700 text-white shadow-md transition-all"
          >
            {isLoading ? (
              <div className="flex items-center space-x-2">
                <svg xmlns="http://www.w3.org/2000/svg" width="18" height="18" viewBox="0 0 24 24" fill="none" stroke="currentColor" strokeWidth="2" strokeLinecap="round" strokeLinejoin="round" className="animate-spin"><path d="M21 12a9 9 0 1 1-6.219-8.56"></path></svg>
                <span>Analyzing...</span>
              </div>
            ) : (
              <div className="flex items-center space-x-2">
                <Layers className="w-4 h-4" />
                <span>Check Equivalence</span>
              </div>
            )}
          </Button>
        </div>

        <div className="mt-6 grid grid-cols-1 md:grid-cols-2 gap-4">
          <CodeEditor
            title="Program 1"
            code={program1}
            onChange={setProgram1}
            height="300px"
          />
          <CodeEditor
            title="Program 2"
            code={program2}
            onChange={setProgram2}
            height="300px"
          />
        </div>
      </div>

      {(isLoading || results) && (
        <AnalysisResults 
          results={results} 
          isLoading={isLoading}
          mode="equivalence"
        />
      )}
    </div>
  );
};

export default EquivalenceMode;