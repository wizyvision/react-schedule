import { TableCell, TableContainer, Box } from '@mui/material';
import { styled } from '@mui/system';

const CalendarContainer = styled(TableContainer)({
  scrollbarWidth: 'none',
  '&::-webkit-scrollbar': {
    display: 'none',
  },
  marginTop: '8px',
  height: 500,
  maxHeight: 600,
  overflowY: 'auto',
  position: 'relative',
});

const Divider = styled(Box)({
  border: 'none'
});

const Resources = styled(TableCell)({
  left: 0,
  position: 'sticky',
  zIndex: 900,
  backgroundColor: 'white',
  minWidth: 200,
  padding: 0,
  borderRight: '1px solid grey',
});

const Resource = styled(Box)({
  border: 'none',
  width: 200,
  paddingLeft: 8,
  paddingRight: 8
});

const Wrapper = styled(Box)({
  display: 'flex',
  alignItems: 'center',
})

const Slots = styled(TableCell)({
  textAlign: 'center',
});

export { CalendarContainer, Divider, Resources, Resource, Wrapper, Slots };
