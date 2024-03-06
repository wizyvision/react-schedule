import { createTheme, alpha } from '@mui/material/styles';

const theme = createTheme({
  palette: {
    primary: {
      main: '#303f9f',
      light: '#5e35b1',
    },
    drop: {
      main: alpha('#303f9f', 0.5),
      light: alpha('#303f9f', 0.35),
      mainTwo: alpha('#5e35b1', 0.5),
      lightTwo: alpha('#5e35b1', 0.35),
    },
    slotBg: {
      main: 'transparent',
    },
    drag: {
      main: '#E0E0E0',
    },
    borderRightColor: {
      main: '#666666',
      light:'rgba(0, 0, 0, 0.05)'
    },
  },
});

export default theme;
