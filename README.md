# SSA-SMT-Analyzer

**SSA-SMT-Analyzer** is a graphical tool that enables formal verification and equivalence checking of simple programs using SSA transformation and SMT solving.  
It parses a custom mini-language, converts code to Static Single Assignment (SSA) form, generates SMT constraints, and uses the Z3 SMT solver to verify correctness and program equivalence.

## 🔗 GitHub Repository
[https://github.com/AbdulMoiz2493/SSA-SMT-Analyzer](https://github.com/AbdulMoiz2493/SSA-SMT-Analyzer)

---

## 🧠 Features

- Parse programs written in a custom mini-language
- Convert programs to SSA form
- Generate SMT constraints from SSA
- Use Z3 SMT solver to:
  - Verify correctness (assertions)
  - Check semantic equivalence of two programs
- Display SSA form, SMT code, and results in the GUI
- Loop unrolling support with user-defined depth
- SSA optimizations (constant propagation, dead code elimination, common subexpression elimination)
- Control Flow Graph (CFG) visualization
- Counterexamples and equivalence examples in the interface

---

## 🗂️ Project Structure

```

SSA-SMT-Analyzer/
│
├── app/                    # Core logic and integration (e.g., Z3 interface, parsing, SSA conversion)
│
├── client/                 # React.js frontend for the GUI
│
├── server/                 # Express.js backend (Node.js)
|    └── z3solver.py         # Python script for SMT solving using Z3
│
├── Report.docx             # Project report/documentation
│
└── .env                    # Environment variables (not committed to repo)

````

---

## 🧪 Environment Setup

### Prerequisites
- Node.js
- MongoDB
- Python 3.10+
- Z3 Solver (`pip install z3-solver`)
- `concurrently` (optional, for dev mode)

### `.env` Configuration

Create a `.env` file at the root of your project with the following:

```env
PORT=5000
PYTHON_PATH=/path/to/your/python3
````

> Replace `/path/to/your/python3` with your actual Python 3 path, e.g., `/usr/bin/python3` or `/Library/Frameworks/Python.framework/...`

---

## 🛠️ Running the Project

### 1. Install Dependencies

```bash
cd client
npm install

cd ../server
npm install
```

### 2. Start the Application

* **Development (with concurrently)**:

```bash
npm run dev
```

* **Or separately**:

```bash
# In one terminal
cd server
npm start

# In another terminal
cd client
npm start
```

---

## 📧 Contact

**Abdul Moiz**
📨 [abdulmoiz8895@gmail.com](mailto:abdulmoiz8895@gmail.com)

---

## 📝 License

MIT License. See [LICENSE](LICENSE) file for details (if applicable).

