import { Table, TableCell, TableContainer } from '@mui/material';
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

const CalendarTable = styled(Table)({
  width: 900,
  overflowX: 'auto',
});

const Divider = styled(TableCell)({
  left: '232px',
  top: 0,
  right: 0,
  position: 'sticky',
  zIndex: 200,
  backgroundColor: 'grey',
  width: '1px',
  border: 'none',
  padding: '1px',
});

const Resources = styled(TableCell)({
  left: 0,
  position: 'sticky',
  zIndex: 900,
  backgroundColor: 'white',
  width: '200px',
  minWidth: '200px',
});

const Slots = styled(TableCell)({
  textAlign: 'center',
});

export { CalendarContainer, CalendarTable, Divider, Resources, Slots };
