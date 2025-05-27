const parseProgram = (code) => {
    // Handle empty or undefined input
    if (!code) return [];
    
    const lines = code.split('\n')
        .map(line => line.trim())
        .filter(line => line);
        
    const ast = [];
    let currentBlock = ast;
    const blockStack = [];

    for (let line of lines) {
        if (!line) continue;

        if (line.startsWith('if')) {
            const condition = line.match(/\((.*?)\)/)?.[1] || '';
            const ifNode = { 
                type: 'if', 
                condition, 
                thenBlock: [], 
                elseBlock: [] 
            };
            currentBlock.push(ifNode);
            blockStack.push(currentBlock);
            currentBlock = ifNode.thenBlock;
        } else if (line.startsWith('else')) {
            // Make sure we have a valid if block to attach to
            if (blockStack.length > 0) {
                const parentBlock = blockStack[blockStack.length - 1];
                const lastNode = parentBlock[parentBlock.length - 1];
                
                if (lastNode && lastNode.type === 'if') {
                    currentBlock = lastNode.elseBlock;
                }
            }
        } else if (line.startsWith('while') || line.startsWith('for')) {
            const condition = line.match(/\((.*?)\)/)?.[1] || '';
            const loopNode = { 
                type: 'loop', 
                condition, 
                block: [],
                value: line 
            };
            currentBlock.push(loopNode);
            blockStack.push(currentBlock);
            currentBlock = loopNode.block;
        } else if (line.startsWith('}')) {
            if (blockStack.length > 0) {
                currentBlock = blockStack.pop();
            }
        } else if (line.startsWith('assert')) {
            const condition = line.match(/\((.*?)\)/)?.[1] || line.replace('assert', '').trim();
            currentBlock.push({ type: 'assert', condition });
        } else if (line.includes(':=') || line.includes('=')) {
            // Support both := and = for assignments
            currentBlock.push({ type: 'assignment', value: line });
        }
    }

    return ast;
};

export default parseProgram;