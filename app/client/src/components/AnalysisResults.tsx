import React, { useEffect, useRef } from "react";
import cytoscape from "cytoscape";
import dagre from "cytoscape-dagre";
import { Card, CardContent, CardHeader, CardTitle } from "@/components/ui/card";
import { Tabs, TabsContent, TabsList, TabsTrigger } from "@/components/ui/tabs";
import { Badge } from "@/components/ui/badge";
import { Separator } from "@/components/ui/separator";
import { AnalysisResponse } from "@/services/api";
import CodeEditor from "./CodeEditor";
import {
  CircleCheck,
  CircleX,
  Code,
  FileText,
  ZoomIn,
  ZoomOut,
  Expand,
} from "lucide-react";

// Register dagre layout
cytoscape.use(dagre);

interface AnalysisResultsProps {
  results: AnalysisResponse | null;
  isLoading: boolean;
  mode: "verification" | "equivalence";
}

const AnalysisResults: React.FC<AnalysisResultsProps> = ({
  results,
  isLoading,
  mode,
}) => {
  const cyRef = useRef<HTMLDivElement>(null);
  const cyInstance = useRef<cytoscape.Core | null>(null);

  useEffect(() => {
    if (!results || !cyRef.current) return;

    if (cyInstance.current) {
      cyInstance.current.destroy();
    }

    const generateGraphData = () => {
      const nodes: cytoscape.NodeDefinition[] = [];
      const edges: cytoscape.EdgeDefinition[] = [];

      const ssa1 = results.ssa.ssa1;
      processSSA(ssa1, nodes, edges, "p1_");

      if (mode === "equivalence" && results.ssa.ssa2) {
        const ssa2 = results.ssa.ssa2;
        processSSA(ssa2, nodes, edges, "p2_");
      }

      return { nodes, edges };
    };

    const processSSA = (
      ssa: any,
      nodes: cytoscape.NodeDefinition[],
      edges: cytoscape.EdgeDefinition[],
      prefix: string
    ) => {
      const variables = new Set<string>();
      const assignments: Record<string, string> = {};

      ssa.optimized.forEach((line: string) => {
        const match = line.match(/(\w+_\d+)\s*=\s*(.+)/);
        if (match) {
          const varName = match[1];
          const expr = match[2];

          if (!variables.has(varName)) {
            nodes.push({
              data: {
                id: prefix + varName,
                label: varName,
                program: prefix === "p1_" ? "Program 1" : "Program 2",
                expr: expr,
              },
              classes: `${prefix === "p1_" ? "program1" : "program2"} ssa-node`,
            });
            variables.add(varName);
          }
          assignments[prefix + varName] = expr;
        }
      });

      Object.entries(assignments).forEach(([targetId, expr]) => {
        const usedVars = expr.match(/\w+_\d+/g) || [];
        usedVars.forEach((sourceVar: string) => {
          const sourceId = prefix + sourceVar;
          if (variables.has(sourceVar)) {
            edges.push({
              data: {
                id: `${sourceId}-${targetId}`,
                source: sourceId,
                target: targetId,
                program: prefix === "p1_" ? "Program 1" : "Program 2",
              },
              classes: `${prefix === "p1_" ? "program1" : "program2"} ssa-edge`,
            });
          }
        });
      });
    };

    const { nodes, edges } = generateGraphData();

    cyInstance.current = cytoscape({
      container: cyRef.current,
      elements: { nodes, edges },
      style: [
        {
          selector: "node",
          style: {
            label: "data(label)",
            "text-valign": "center",
            "text-halign": "center",
            width: 50,
            height: 50,
            "font-size": 12,
            "background-color": "#64748b",
            "text-outline-color": "#64748b",
            "text-outline-width": 2,
            color: "#fff",
            "border-width": 2,
            "border-color": "#fff",
            shape: "ellipse",
          },
        },
        {
          selector: "node.ssa-node",
          style: {
            "text-wrap": "wrap",
            "text-max-width": "80px",
            "text-overflow-wrap": "anywhere",
          },
        },
        {
          selector: "edge",
          style: {
            width: 2,
            "line-color": "#94a3b8",
            "curve-style": "bezier",
            "target-arrow-shape": "triangle",
            "target-arrow-color": "#94a3b8",
            "arrow-scale": 0.8,
          },
        },
        {
          selector: ".program1",
          style: {
            "background-color": "#3b82f6",
            "text-outline-color": "#3b82f6",
          },
        },
        {
          selector: ".program2",
          style: {
            "background-color": "#8b5cf6",
            "text-outline-color": "#8b5cf6",
          },
        },
        {
          selector: ":selected",
          style: {
            "background-color": "#f59e0b",
            "line-color": "#f59e0b",
            "target-arrow-color": "#f59e0b",
            "text-outline-color": "#f59e0b",
          },
        },
      ],
      layout: {
        name: "dagre",
      },
      userZoomingEnabled: true,
      userPanningEnabled: true,
      boxSelectionEnabled: true,
      wheelSensitivity: 0.2,
    });

    cyInstance.current.on("ready", () => {
      if (cyInstance.current) {
        cyInstance.current.fit();
      }
    });

    cyInstance.current.on("mouseover", "node", (event) => {
      const node = event.target;
      node.qtip({
        content: `Expression: ${node.data("expr")}`,
        position: {
          my: "top center",
          at: "bottom center",
        },
        style: {
          classes: "qtip-bootstrap",
          tip: {
            width: 16,
            height: 8,
          },
        },
        show: {
          event: event.type,
          ready: true,
        },
        hide: {
          event: "mouseout unfocus",
        },
      });
    });

    return () => {
      if (cyInstance.current) {
        cyInstance.current.destroy();
      }
    };
  }, [results, mode]);

  const handleZoomIn = () => {
    if (cyInstance.current) {
      cyInstance.current.zoom(cyInstance.current.zoom() * 1.2);
    }
  };

  const handleZoomOut = () => {
    if (cyInstance.current) {
      cyInstance.current.zoom(cyInstance.current.zoom() * 0.8);
    }
  };

  const handleFit = () => {
    if (cyInstance.current) {
      cyInstance.current.fit();
    }
  };

  if (isLoading) {
    return (
      <div className="flex justify-center items-center h-60 bg-slate-50 dark:bg-slate-800/50 rounded-xl border border-slate-100 dark:border-slate-800">
        <div className="flex flex-col items-center">
          <div className="w-12 h-12 rounded-full border-4 border-t-indigo-600 border-slate-200 animate-spin"></div>
          <p className="mt-4 text-indigo-600 dark:text-indigo-400 font-medium">
            ZORO is analyzing your program...
          </p>
        </div>
      </div>
    );
  }

  if (!results) {
    return null;
  }

  const { ssa, smt, status, results: analysisResults } = results;

  const isVerified = analysisResults
    ? mode === "equivalence"
      ? analysisResults.verified
      : analysisResults.verified
    : false;

  const formatExamples = (examples: Record<string, string> | { result: string } | string | undefined) => {
    console.log('Formatting examples:', examples);

    if (!examples) {
      return (
        <p className="text-slate-500 dark:text-slate-400">
          No satisfying examples available. The program may have no valid inputs that satisfy the assertions.
        </p>
      );
    }

    if (typeof examples === 'string') {
      return (
        <div className="bg-white dark:bg-slate-800 p-4 rounded-lg border border-slate-200 dark:border-slate-700 shadow-sm">
          <h4 className="font-medium text-sm mb-2 flex items-center text-slate-700 dark:text-slate-300">
            <div className="mr-2 p-1 rounded-full bg-emerald-100 dark:bg-emerald-900/30">
              <CircleCheck className="h-4 w-4 text-emerald-600 dark:text-emerald-400" />
            </div>
            {examples === 'Satisfiable'
              ? mode === 'equivalence'
                ? 'Programs are equivalent for some inputs'
                : 'Program assertions are satisfiable'
              : examples}
          </h4>
        </div>
      );
    }

    if ('result' in examples) {
      return (
        <div className="bg-white dark:bg-slate-800 p-4 rounded-lg border border-slate-200 dark:border-slate-700 shadow-sm">
          <h4 className="font-medium text-sm mb-2 flex items-center text-slate-700 dark:text-slate-300">
            <div className="mr-2 p-1 rounded-full bg-emerald-100 dark:bg-emerald-900/30">
              <CircleCheck className="h-4 w-4 text-emerald-600 dark:text-emerald-400" />
            </div>
            {examples.result === 'Satisfiable'
              ? mode === 'equivalence'
                ? 'Programs are equivalent for some inputs'
                : 'Program assertions are satisfiable'
              : examples.result}
          </h4>
        </div>
      );
    }

    if (Object.keys(examples).length === 0) {
      return (
        <p className="text-slate-500 dark:text-slate-400">
          No specific satisfying examples found. The program is satisfiable but no variable assignments were provided.
        </p>
      );
    }

    return (
      <div className="space-y-2">
        <div className="bg-white dark:bg-slate-800 p-4 rounded-lg border border-slate-200 dark:border-slate-700 shadow-sm">
          <h4 className="font-medium text-sm mb-2 flex items-center text-slate-700 dark:text-slate-300">
            <div className="mr-2 p-1 rounded-full bg-emerald-100 dark:bg-emerald-900/30">
              <CircleCheck className="h-4 w-4 text-emerald-600 dark:text-emerald-400" />
            </div>
            {mode === "equivalence" ? "Equivalent Example" : "Satisfying Example"}
          </h4>
          <div className="grid grid-cols-2 gap-3">
            {Object.entries(examples).map(([variable, value]) => (
              <div
                key={variable}
                className="text-sm bg-slate-50 dark:bg-slate-800/80 p-2 rounded border border-slate-100 dark:border-slate-700"
              >
                <span className="font-mono">
                  <span className="text-purple-600 dark:text-purple-400">
                    {variable}
                  </span>{" "}
                  =
                  <span className="text-indigo-600 dark:text-indigo-400">
                    {" "}
                    {value}
                  </span>
                </span>
              </div>
            ))}
          </div>
        </div>
      </div>
    );
  };

  const formatCounterexamples = (
    counterexample: Record<string, string> | string | undefined
  ) => {
    console.log('Formatting counterexamples:', counterexample);

    if (!counterexample) {
      return (
        <p className="text-slate-500 dark:text-slate-400">
          No counterexamples available. The program may be verified or no counterexamples were found.
        </p>
      );
    }

    if (typeof counterexample === 'string') {
      return (
        <div className="bg-white dark:bg-slate-800 p-4 rounded-lg border border-slate-200 dark:border-slate-700 shadow-sm">
          <h4 className="font-medium text-sm mb-2 flex items-center text-slate-700 dark:text-slate-300">
            <div className="mr-2 p-1 rounded-full bg-red-100 dark:bg-red-900/30">
              <CircleX className="h-4 w-4 text-red-600 dark:text-red-400" />
            </div>
            {counterexample}
          </h4>
        </div>
      );
    }

    if (Object.keys(counterexample).length === 0) {
      return (
        <p className="text-slate-500 dark:text-slate-400">
          No specific counterexamples found. The program may not have any failing cases.
        </p>
      );
    }

    return (
      <div className="space-y-3">
        <div className="bg-white dark:bg-slate-800 p-4 rounded-lg border border-slate-200 dark:border-slate-700 shadow-sm">
          <h4 className="font-medium text-sm mb-2 flex items-center text-slate-700 dark:text-slate-300">
            <div className="mr-2 p-1 rounded-full bg-red-100 dark:bg-red-900/30">
              <CircleX className="h-4 w-4 text-red-600 dark:text-red-400" />
            </div>
            Counterexample
          </h4>
          <div className="grid grid-cols-2 gap-3">
            {Object.entries(counterexample).map(([variable, value]) => (
              <div
                key={variable}
                className="text-sm bg-slate-50 dark:bg-slate-800/80 p-2 rounded border border-slate-100 dark:border-slate-700"
              >
                <span className="font-mono">
                  <span className="text-purple-600 dark:text-purple-400">
                    {variable}
                  </span>{" "}
                  =
                  <span className="text-indigo-600 dark:text-indigo-400">
                    {" "}
                    {value}
                  </span>
                </span>
              </div>
            ))}
          </div>
        </div>
      </div>
    );
  };

  return (
    <div className="space-y-6">
      <Card className="overflow-hidden border-0 shadow-lg">
        <CardHeader
          className={`
          ${
            isVerified
              ? "bg-gradient-to-r from-emerald-600 to-teal-600"
              : "bg-gradient-to-r from-red-600 to-rose-600"
          } 
          text-white`}
        >
          <div className="flex justify-between items-center">
            <div className="flex items-center">
              {isVerified ? (
                <CircleCheck className="mr-2 h-5 w-5" />
              ) : (
                <CircleX className="mr-2 h-5 w-5" />
              )}
              <CardTitle>Analysis Result</CardTitle>
            </div>
            <Badge
              variant={isVerified ? "default" : "destructive"}
              className="text-sm py-1 px-3"
            >
              {isVerified ? "VERIFIED ✓" : "NOT VERIFIED ✗"}
            </Badge>
          </div>
        </CardHeader>
        <CardContent className="p-0">
          <Tabs defaultValue="examples" className="w-full">
            <TabsList className="w-full rounded-none grid grid-cols-2 bg-slate-100 dark:bg-slate-800">
              <TabsTrigger
                value="examples"
                className="rounded-none data-[state=active]:bg-white dark:data-[state=active]:bg-slate-700"
              >
                {mode === "verification"
                  ? "Satisfying Examples"
                  : "Equivalent Examples"}
              </TabsTrigger>
              <TabsTrigger
                value="counterexamples"
                className="rounded-none data-[state=active]:bg-white dark:data-[state=active]:bg-slate-700"
              >
                Counterexamples
              </TabsTrigger>
            </TabsList>
            <div className="p-6">
              <TabsContent value="examples" className="mt-0">
                {formatExamples(analysisResults?.model)}
              </TabsContent>
              <TabsContent value="counterexamples" className="mt-0">
                {formatCounterexamples(analysisResults?.counterexample)}
              </TabsContent>
            </div>
          </Tabs>
        </CardContent>
      </Card>

      <div className="grid grid-cols-1 md:grid-cols-2 gap-6">
        <div className="space-y-4">
          <div className="flex items-center gap-2 text-lg font-medium text-slate-800 dark:text-slate-200">
            <Code className="h-5 w-5 text-indigo-600 dark:text-indigo-400" />
            <h3>SSA Transformation</h3>
          </div>
          <Tabs defaultValue="graph" className="w-full">
            <TabsList className="w-full grid grid-cols-3 bg-slate-100 dark:bg-slate-800">
              <TabsTrigger value="graph">SSA Graph</TabsTrigger>
              <TabsTrigger value="transformed">SSA Transformed</TabsTrigger>
              <TabsTrigger value="optimized">SSA Optimized</TabsTrigger>
            </TabsList>
            <TabsContent value="graph" className="mt-4 relative">
              <div
                ref={cyRef}
                className="w-full h-[500px] border rounded-lg bg-white dark:bg-slate-900 border-slate-200 dark:border-slate-700 shadow-sm"
              />
              <div className="absolute right-4 top-4 flex flex-col space-y-2 z-10">
                <button
                  onClick={handleZoomIn}
                  className="p-2 rounded-full bg-white dark:bg-slate-800 shadow-md hover:bg-slate-100 dark:hover:bg-slate-700 transition-colors"
                  aria-label="Zoom in"
                >
                  <ZoomIn className="h-4 w-4 text-slate-700 dark:text-slate-300" />
                </button>
                <button
                  onClick={handleZoomOut}
                  className="p-2 rounded-full bg-white dark:bg-slate-800 shadow-md hover:bg-slate-100 dark:hover:bg-slate-700 transition-colors"
                  aria-label="Zoom out"
                >
                  <ZoomOut className="h-4 w-4 text-slate-700 dark:text-slate-300" />
                </button>
                <button
                  onClick={handleFit}
                  className="p-2 rounded-full bg-white dark:bg-slate-800 shadow-md hover:bg-slate-100 dark:hover:bg-slate-700 transition-colors"
                  aria-label="Fit to screen"
                >
                  <Expand className="h-4 w-4 text-slate-700 dark:text-slate-300" />
                </button>
              </div>
            </TabsContent>
            <TabsContent value="transformed" className="mt-4 space-y-4">
              <CodeEditor
                title="SSA - Program 1"
                code={results.ssa.ssa1.transformed.join("\n")}
                onChange={() => {}}
                readOnly
                height="250px"
              />
              {mode === "equivalence" && results.ssa.ssa2 && (
                <CodeEditor
                  title="SSA - Program 2"
                  code={results.ssa.ssa2.transformed.join("\n")}
                  onChange={() => {}}
                  readOnly
                  height="250px"
                />
              )}
            </TabsContent>
            <TabsContent value="optimized" className="mt-4 space-y-4">
              <CodeEditor
                title="Optimized SSA - Program 1"
                code={results.ssa.ssa1.optimized.join("\n")}
                onChange={() => {}}
                readOnly
                height="250px"
              />
              {mode === "equivalence" && results.ssa.ssa2 && (
                <CodeEditor
                  title="Optimized SSA - Program 2"
                  code={results.ssa.ssa2.optimized.join("\n")}
                  onChange={() => {}}
                  readOnly
                  height="250px"
                />
              )}
            </TabsContent>
          </Tabs>
        </div>

        <div className="space-y-4">
          <div className="flex items-center gap-2 text-lg font-medium text-slate-800 dark:text-slate-200">
            <FileText className="h-5 w-5 text-purple-600 dark:text-purple-400" />
            <h3>SMT Constraints</h3>
          </div>
          <CodeEditor
            title="SMT Code"
            code={smt}
            onChange={() => {}}
            readOnly
            height="555px"
            className="border-indigo-100 dark:border-indigo-900/30"
          />
        </div>
      </div>
    </div>
  );
};

export default AnalysisResults;