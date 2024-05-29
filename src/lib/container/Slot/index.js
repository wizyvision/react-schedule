import { TableCell, useTheme } from '@mui/material';
import { HEIGHT } from '../../constants/appointment';
import { useSchedulerContext } from '../../context/SchedulerProvider';
import { styled } from '@mui/system';

const Slot = styled(TableCell)((props) => {
  const { index, width } = props;
  const { SlotProps, } = useSchedulerContext()
  const { style } = SlotProps || {};
  const theme = useTheme()

  // const borderRightColor = () => {
  //   let color = theme.palette.borderRightColor.light
  //   switch (secondaryDuration) {
  //     case 15:
  //       color = index % 4 !== 3 ? 
  //       theme.palette.borderRightColor.light
  //       : theme.palette.borderRightColor.main; 
  //       break;
  //     default:
  //       color = index % 2 !== 1 ? 
  //       theme.palette.borderRightColor.light
  //       : theme.palette.borderRightColor.main; 
  //       break;
  //   }
  //   return color;
  // };

  // const borderRightStyle = () => {
  //   switch (secondaryDuration) {
  //     case 15:
  //       if (index % 2 !== 1) {
  //         return 'none';
  //       }
  //       return 'solid';
  //     default:
  //       return 'solid';
  //   }
  // };

  return {
    paddingTop: theme.spacing(1.05),
    paddingBottom: theme.spacing(1.05),
    paddingLeft: 0,
    paddingRight: 0,
    position: 'relative',
    width: width,
    height: HEIGHT,
    overflow: 'visible',
    verticalAlign: 'top',
    borderRightWidth: '1px',
    borderRightStyle: 'solid',
    borderRightColor: 'rgba(0, 0, 0, 0.05)',
    // borderRightStyle: borderRightStyle(),
    ...style,
  };
});

export default Slot;
