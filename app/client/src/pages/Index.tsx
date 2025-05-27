
import React, { useState } from 'react';
import {
  Card,
  CardContent,
  CardDescription,
  CardHeader,
  CardTitle,
} from "@/components/ui/card";
import { Tabs, TabsContent, TabsList, TabsTrigger } from "@/components/ui/tabs";
import VerificationMode from '@/components/VerificationMode';
import EquivalenceMode from '@/components/EquivalenceMode';

const Index = () => {
  const [mode, setMode] = useState<'verification' | 'equivalence'>('verification');

  return (
    <div className="min-h-screen bg-gradient-to-br from-slate-50 to-slate-100 dark:from-slate-900 dark:to-slate-800 py-8 px-4">
      <div className="container mx-auto max-w-7xl">
        <div className="text-center mb-8">
          <h1 className="text-4xl font-bold bg-clip-text text-transparent bg-gradient-to-r from-indigo-600 to-purple-600">
            ZORO Analyzer
          </h1>
          <p className="text-slate-600 dark:text-slate-400 mt-2">
            Advanced program analysis tool for verification and equivalence checking
          </p>
        </div>
        
        <Card className="border-0 shadow-xl overflow-hidden">
          <CardHeader className="bg-gradient-to-r from-indigo-600 to-purple-600 text-white">
            <div className="flex items-center">
              <div className="mr-3">
                <svg xmlns="http://www.w3.org/2000/svg" width="24" height="24" viewBox="0 0 24 24" fill="none" stroke="currentColor" strokeWidth="2" strokeLinecap="round" strokeLinejoin="round" className="lucide-code"><polyline points="16 18 22 12 16 6"></polyline><polyline points="8 6 2 12 8 18"></polyline></svg>
              </div>
              <div>
                <CardTitle className="text-2xl">ZORO Formal Verification</CardTitle>
                <CardDescription className="text-indigo-100">
                  Rigorously analyze program correctness and equivalence
                </CardDescription>
              </div>
            </div>
          </CardHeader>
          <CardContent className="p-6">
            <Tabs 
              defaultValue="verification" 
              className="w-full"
              onValueChange={(value) => setMode(value as 'verification' | 'equivalence')}
            >
              <TabsList className="grid w-full grid-cols-2 mb-6 bg-slate-100 dark:bg-slate-800 p-1 rounded-lg">
                <TabsTrigger 
                  value="verification" 
                  className="data-[state=active]:bg-white dark:data-[state=active]:bg-slate-700 data-[state=active]:text-indigo-600 dark:data-[state=active]:text-indigo-400 rounded-md"
                >
                  <div className="flex items-center space-x-2 py-1">
                    <svg xmlns="http://www.w3.org/2000/svg" width="18" height="18" viewBox="0 0 24 24" fill="none" stroke="currentColor" strokeWidth="2" strokeLinecap="round" strokeLinejoin="round" className="lucide-search"><circle cx="11" cy="11" r="8"></circle><path d="m21 21-4.3-4.3"></path></svg>
                    <span>Verification Mode</span>
                  </div>
                </TabsTrigger>
                <TabsTrigger 
                  value="equivalence" 
                  className="data-[state=active]:bg-white dark:data-[state=active]:bg-slate-700 data-[state=active]:text-indigo-600 dark:data-[state=active]:text-indigo-400 rounded-md"
                >
                  <div className="flex items-center space-x-2 py-1">
                    <svg xmlns="http://www.w3.org/2000/svg" width="18" height="18" viewBox="0 0 24 24" fill="none" stroke="currentColor" strokeWidth="2" strokeLinecap="round" strokeLinejoin="round" className="lucide-layers"><path d="m12.83 2.18a2 2 0 0 0-1.66 0L2.6 6.08a1 1 0 0 0 0 1.83l8.58 3.91a2 2 0 0 0 1.66 0l8.58-3.9a1 1 0 0 0 0-1.83Z"></path><path d="m22 11-8.58 3.91a2 2 0 0 1-1.66 0L3.17 11"></path><path d="m22 16-8.58 3.91a2 2 0 0 1-1.66 0L3.17 16"></path></svg>
                    <span>Equivalence Mode</span>
                  </div>
                </TabsTrigger>
              </TabsList>
              <div className="p-1">
                <TabsContent value="verification">
                  <VerificationMode />
                </TabsContent>
                <TabsContent value="equivalence">
                  <EquivalenceMode />
                </TabsContent>
              </div>
            </Tabs>
          </CardContent>
        </Card>
        
        <div className="text-center mt-8 text-sm text-slate-500">
          ZORO Analyzer v1.0 — Formal verification and program analysis tool
        </div>
      </div>
    </div>
  );
};

export default Index;
