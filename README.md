## **Getting Started**

Created a package, ```@wizyvision/react-schedule```, to accommodate the necessary features for Scheduling Dashboard:

- **Resource Timeline**
  - Assign appointment to user and time slot
  - Assign an appointment with respective duration
- **Drag and drop**
  - From outside and to inside of ```Resource Timeline```
  - Across the ```Resource Timeline```
 
### Installation
---
**Yarn**
```
yarn add react-dnd
yarn add react-dnd-html5-backend
yarn add @wizyvision/react-schedule          
```

**NPM**
```
npm install react-dnd
npm install react-dnd-html5-backend
npm install @wizyvision/react-schedule       
```

### Usage
---
1. Import the packages
```
import { DndProvider } from 'react-dnd';
import { HTML5Backend } from 'react-dnd-html5-backend';
import Scheduler from '@wizyvision/react-schedule'
```

