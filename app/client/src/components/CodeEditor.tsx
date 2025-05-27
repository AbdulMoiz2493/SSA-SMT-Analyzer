
import React from 'react';
import { Textarea } from "@/components/ui/textarea";
import { Card, CardContent, CardHeader, CardTitle } from "@/components/ui/card";

interface CodeEditorProps {
  title: string;
  code: string;
  onChange: (value: string) => void;
  readOnly?: boolean;
  className?: string;
  height?: string;
}

const CodeEditor: React.FC<CodeEditorProps> = ({
  title,
  code,
  onChange,
  readOnly = false,
  className = "",
  height = "300px"
}) => {
  return (
    <Card className={`shadow-lg border border-slate-200 dark:border-slate-700 ${className}`}>
      <CardHeader className="bg-gradient-to-r from-indigo-600 to-purple-600 py-2 px-4 rounded-t-lg">
        <CardTitle className="text-sm font-medium text-white">{title}</CardTitle>
      </CardHeader>
      <CardContent className="p-0">
        <Textarea
          value={code}
          onChange={(e) => onChange(e.target.value)}
          readOnly={readOnly}
          className="font-mono text-sm h-full rounded-none border-0 focus-visible:ring-0 focus-visible:ring-offset-0 bg-slate-50 dark:bg-slate-900"
          style={{ 
            height, 
            resize: 'none',
            backgroundColor: readOnly ? 'rgb(248 250 252)' : 'white'
          }}
        />
      </CardContent>
    </Card>
  );
};

export default CodeEditor;
